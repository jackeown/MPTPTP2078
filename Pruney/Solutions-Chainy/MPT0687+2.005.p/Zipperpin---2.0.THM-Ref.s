%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AzH03ILs7M

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:11 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   81 (  99 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  657 ( 865 expanded)
%              Number of equality atoms :   52 (  70 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('0',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X10 @ X10 @ X11 @ X12 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      | ( r2_hidden @ X49 @ X55 )
      | ( X55
       != ( k3_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( r2_hidden @ X49 @ ( k3_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50 ) )
      | ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X43 != X42 )
      | ~ ( zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X42: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ~ ( zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X42 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('17',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ~ ( r2_hidden @ X70 @ X69 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X70 @ X68 ) @ X70 ) @ X68 )
      | ( X69
       != ( k2_relat_1 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('18',plain,(
    ! [X68: $i,X70: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X70 @ X68 ) @ X70 ) @ X68 )
      | ~ ( r2_hidden @ X70 @ ( k2_relat_1 @ X68 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_B ) @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X59: $i,X60: $i,X62: $i,X64: $i,X65: $i] :
      ( ( X62
       != ( k10_relat_1 @ X60 @ X59 ) )
      | ( r2_hidden @ X64 @ X62 )
      | ~ ( r2_hidden @ ( k4_tarski @ X64 @ X65 ) @ X60 )
      | ~ ( r2_hidden @ X65 @ X59 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('21',plain,(
    ! [X59: $i,X60: $i,X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X60 )
      | ~ ( r2_hidden @ X65 @ X59 )
      | ~ ( r2_hidden @ ( k4_tarski @ X64 @ X65 ) @ X60 )
      | ( r2_hidden @ X64 @ ( k10_relat_1 @ X60 @ X59 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_zfmisc_1 @ X38 @ X39 )
        = k1_xboole_0 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X38: $i] :
      ( ( k2_zfmisc_1 @ X38 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X40: $i,X41: $i] :
      ~ ( r2_hidden @ X40 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
      | ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X73 ) @ X74 )
      | ( ( k10_relat_1 @ X73 @ X74 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AzH03ILs7M
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 671 iterations in 0.298s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.74  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.51/0.74  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.51/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.51/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.74  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.51/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.74  thf(t142_funct_1, conjecture,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ B ) =>
% 0.51/0.74       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.51/0.74         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i]:
% 0.51/0.74        ( ( v1_relat_1 @ B ) =>
% 0.51/0.74          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.51/0.74            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.51/0.74        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.51/0.74       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.51/0.74         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf(t69_enumset1, axiom,
% 0.51/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.74  thf('3', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.51/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.74  thf(t70_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.74  thf('4', plain,
% 0.51/0.74      (![X8 : $i, X9 : $i]:
% 0.51/0.74         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.74  thf(t71_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.74         ((k2_enumset1 @ X10 @ X10 @ X11 @ X12)
% 0.51/0.74           = (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.51/0.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.51/0.74  thf(t72_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.74         ((k3_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.51/0.74           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.51/0.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.74  thf(d3_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.74     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.51/0.74       ( ![G:$i]:
% 0.51/0.74         ( ( r2_hidden @ G @ F ) <=>
% 0.51/0.74           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.51/0.74                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_2, axiom,
% 0.51/0.74    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.51/0.74       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.51/0.74         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_3, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.74     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.51/0.74       ( ![G:$i]:
% 0.51/0.74         ( ( r2_hidden @ G @ F ) <=>
% 0.51/0.74           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.51/0.74          | (r2_hidden @ X49 @ X55)
% 0.51/0.74          | ((X55) != (k3_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.74  thf('8', plain,
% 0.51/0.74      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.51/0.74         ((r2_hidden @ X49 @ (k3_enumset1 @ X54 @ X53 @ X52 @ X51 @ X50))
% 0.51/0.74          | (zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.51/0.74      inference('simplify', [status(thm)], ['7'])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.74         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.51/0.74          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.51/0.74      inference('sup+', [status(thm)], ['6', '8'])).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.51/0.74         (((X43) != (X42))
% 0.51/0.74          | ~ (zip_tseitin_0 @ X43 @ X44 @ X45 @ X46 @ X47 @ X42))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.74  thf('11', plain,
% 0.51/0.74      (![X42 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.51/0.74         ~ (zip_tseitin_0 @ X42 @ X44 @ X45 @ X46 @ X47 @ X42)),
% 0.51/0.74      inference('simplify', [status(thm)], ['10'])).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.74         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.51/0.74      inference('sup-', [status(thm)], ['9', '11'])).
% 0.51/0.74  thf('13', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['5', '12'])).
% 0.51/0.74  thf('14', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '13'])).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.51/0.74        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('split', [status(esa)], ['15'])).
% 0.51/0.74  thf(d5_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.51/0.74       ( ![C:$i]:
% 0.51/0.74         ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.74           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X70 @ X69)
% 0.51/0.74          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X70 @ X68) @ X70) @ X68)
% 0.51/0.74          | ((X69) != (k2_relat_1 @ X68)))),
% 0.51/0.74      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X68 : $i, X70 : $i]:
% 0.51/0.74         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X70 @ X68) @ X70) @ X68)
% 0.51/0.74          | ~ (r2_hidden @ X70 @ (k2_relat_1 @ X68)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['17'])).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_A @ sk_B) @ sk_A) @ sk_B))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['16', '18'])).
% 0.51/0.74  thf(d14_relat_1, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ A ) =>
% 0.51/0.74       ( ![B:$i,C:$i]:
% 0.51/0.74         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.51/0.74           ( ![D:$i]:
% 0.51/0.74             ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.74               ( ?[E:$i]:
% 0.51/0.74                 ( ( r2_hidden @ E @ B ) & 
% 0.51/0.74                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      (![X59 : $i, X60 : $i, X62 : $i, X64 : $i, X65 : $i]:
% 0.51/0.74         (((X62) != (k10_relat_1 @ X60 @ X59))
% 0.51/0.74          | (r2_hidden @ X64 @ X62)
% 0.51/0.74          | ~ (r2_hidden @ (k4_tarski @ X64 @ X65) @ X60)
% 0.51/0.74          | ~ (r2_hidden @ X65 @ X59)
% 0.51/0.74          | ~ (v1_relat_1 @ X60))),
% 0.51/0.74      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X59 : $i, X60 : $i, X64 : $i, X65 : $i]:
% 0.51/0.74         (~ (v1_relat_1 @ X60)
% 0.51/0.74          | ~ (r2_hidden @ X65 @ X59)
% 0.51/0.74          | ~ (r2_hidden @ (k4_tarski @ X64 @ X65) @ X60)
% 0.51/0.74          | (r2_hidden @ X64 @ (k10_relat_1 @ X60 @ X59)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['20'])).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 0.51/0.74           | ~ (r2_hidden @ sk_A @ X0)
% 0.51/0.74           | ~ (v1_relat_1 @ sk_B)))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['19', '21'])).
% 0.51/0.74  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 0.51/0.74           | ~ (r2_hidden @ sk_A @ X0)))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('demod', [status(thm)], ['22', '23'])).
% 0.51/0.74  thf('25', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ 
% 0.51/0.74           (k10_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['14', '24'])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ 
% 0.51/0.74         (k10_relat_1 @ sk_B @ (k1_tarski @ sk_A))))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('sup+', [status(thm)], ['3', '25'])).
% 0.51/0.74  thf('27', plain,
% 0.51/0.74      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B) @ k1_xboole_0))
% 0.51/0.74         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.51/0.74             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.51/0.74      inference('sup+', [status(thm)], ['2', '26'])).
% 0.51/0.74  thf(t113_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.51/0.74  thf('28', plain,
% 0.51/0.74      (![X38 : $i, X39 : $i]:
% 0.51/0.74         (((k2_zfmisc_1 @ X38 @ X39) = (k1_xboole_0))
% 0.51/0.74          | ((X39) != (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      (![X38 : $i]: ((k2_zfmisc_1 @ X38 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.51/0.74  thf(t152_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      (![X40 : $i, X41 : $i]: ~ (r2_hidden @ X40 @ (k2_zfmisc_1 @ X40 @ X41))),
% 0.51/0.74      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.51/0.74  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.51/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.51/0.74       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['27', '31'])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.51/0.74       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.51/0.74      inference('split', [status(esa)], ['15'])).
% 0.51/0.74  thf(l27_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X35 : $i, X36 : $i]:
% 0.51/0.74         ((r1_xboole_0 @ (k1_tarski @ X35) @ X36) | (r2_hidden @ X35 @ X36))),
% 0.51/0.74      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.51/0.74  thf(symmetry_r1_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.51/0.74      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.74  thf(t173_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ B ) =>
% 0.51/0.74       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.74         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (![X73 : $i, X74 : $i]:
% 0.51/0.74         (~ (r1_xboole_0 @ (k2_relat_1 @ X73) @ X74)
% 0.51/0.74          | ((k10_relat_1 @ X73 @ X74) = (k1_xboole_0))
% 0.51/0.74          | ~ (v1_relat_1 @ X73))),
% 0.51/0.74      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.51/0.74          | ~ (v1_relat_1 @ X1)
% 0.51/0.74          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.51/0.74         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.51/0.74         | ~ (v1_relat_1 @ sk_B)))
% 0.51/0.74         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.74  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('42', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.51/0.74         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.51/0.74         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.51/0.74      inference('split', [status(esa)], ['15'])).
% 0.51/0.74  thf('44', plain,
% 0.51/0.74      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.51/0.74         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) & 
% 0.51/0.74             ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.51/0.74  thf('45', plain,
% 0.51/0.74      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.51/0.74       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.51/0.74      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.74  thf('46', plain, ($false),
% 0.51/0.74      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '45'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
