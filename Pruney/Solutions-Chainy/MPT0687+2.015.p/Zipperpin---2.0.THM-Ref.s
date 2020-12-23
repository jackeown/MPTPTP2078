%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jYtU9hWLtL

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:12 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   71 (  91 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  580 ( 805 expanded)
%              Number of equality atoms :   49 (  68 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k10_relat_1 @ X50 @ X51 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X50 ) @ X51 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('6',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
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

thf('16',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X41 @ X47 )
      | ( X47
       != ( k3_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X41 @ ( k3_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 ) )
      | ( zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X35 != X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X34: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X36 @ X37 @ X38 @ X39 @ X34 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( ( k10_relat_1 @ X50 @ X51 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jYtU9hWLtL
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.83/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.07  % Solved by: fo/fo7.sh
% 0.83/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.07  % done 1521 iterations in 0.637s
% 0.83/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.07  % SZS output start Refutation
% 0.83/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.07  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.83/1.07  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.83/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.07  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.83/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.83/1.07  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.83/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.07  thf(t142_funct_1, conjecture,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ B ) =>
% 0.83/1.07       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.83/1.07         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.07    (~( ![A:$i,B:$i]:
% 0.83/1.07        ( ( v1_relat_1 @ B ) =>
% 0.83/1.07          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.83/1.07            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.83/1.07    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.83/1.07  thf('0', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.83/1.07        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('1', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.83/1.07       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.83/1.07      inference('split', [status(esa)], ['0'])).
% 0.83/1.07  thf('2', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.83/1.07        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('3', plain,
% 0.83/1.07      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.83/1.07         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.83/1.07      inference('split', [status(esa)], ['2'])).
% 0.83/1.07  thf('4', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.83/1.07         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('split', [status(esa)], ['0'])).
% 0.83/1.07  thf(t173_relat_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ B ) =>
% 0.83/1.07       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.83/1.07         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.83/1.07  thf('5', plain,
% 0.83/1.07      (![X50 : $i, X51 : $i]:
% 0.83/1.07         (((k10_relat_1 @ X50 @ X51) != (k1_xboole_0))
% 0.83/1.07          | (r1_xboole_0 @ (k2_relat_1 @ X50) @ X51)
% 0.83/1.07          | ~ (v1_relat_1 @ X50))),
% 0.83/1.07      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.83/1.07  thf('6', plain,
% 0.83/1.07      (((((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.07         | ~ (v1_relat_1 @ sk_B)
% 0.83/1.07         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.83/1.07         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.07  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('8', plain,
% 0.83/1.07      (((((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.07         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.83/1.07         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('demod', [status(thm)], ['6', '7'])).
% 0.83/1.07  thf('9', plain,
% 0.83/1.07      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.83/1.07         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['8'])).
% 0.83/1.07  thf(symmetry_r1_xboole_0, axiom,
% 0.83/1.07    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.83/1.07  thf('10', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.83/1.07  thf('11', plain,
% 0.83/1.07      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.83/1.07         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.83/1.07  thf(t69_enumset1, axiom,
% 0.83/1.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.83/1.07  thf('12', plain,
% 0.83/1.07      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.83/1.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.07  thf(t70_enumset1, axiom,
% 0.83/1.07    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.83/1.07  thf('13', plain,
% 0.83/1.07      (![X12 : $i, X13 : $i]:
% 0.83/1.07         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.83/1.07      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.83/1.07  thf(t71_enumset1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.83/1.07  thf('14', plain,
% 0.83/1.07      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.07         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.83/1.07           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.83/1.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.83/1.07  thf(t72_enumset1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.07     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.83/1.07  thf('15', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.83/1.07         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.83/1.07           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.83/1.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.83/1.07  thf(d3_enumset1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.83/1.07     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.83/1.07       ( ![G:$i]:
% 0.83/1.07         ( ( r2_hidden @ G @ F ) <=>
% 0.83/1.07           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.83/1.07                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.83/1.07  thf(zf_stmt_2, axiom,
% 0.83/1.07    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.83/1.07     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.83/1.07       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.83/1.07         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_3, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.83/1.07     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.83/1.07       ( ![G:$i]:
% 0.83/1.07         ( ( r2_hidden @ G @ F ) <=>
% 0.83/1.07           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.83/1.07  thf('16', plain,
% 0.83/1.07      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.83/1.07         ((zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.83/1.07          | (r2_hidden @ X41 @ X47)
% 0.83/1.07          | ((X47) != (k3_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.83/1.07  thf('17', plain,
% 0.83/1.07      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.83/1.07         ((r2_hidden @ X41 @ (k3_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42))
% 0.83/1.07          | (zip_tseitin_0 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 0.83/1.07      inference('simplify', [status(thm)], ['16'])).
% 0.83/1.07  thf('18', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.83/1.07         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.83/1.07          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.83/1.07      inference('sup+', [status(thm)], ['15', '17'])).
% 0.83/1.07  thf('19', plain,
% 0.83/1.07      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.83/1.07         (((X35) != (X34))
% 0.83/1.07          | ~ (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X34))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.83/1.07  thf('20', plain,
% 0.83/1.07      (![X34 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.83/1.07         ~ (zip_tseitin_0 @ X34 @ X36 @ X37 @ X38 @ X39 @ X34)),
% 0.83/1.07      inference('simplify', [status(thm)], ['19'])).
% 0.83/1.07  thf('21', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.07         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.83/1.07      inference('sup-', [status(thm)], ['18', '20'])).
% 0.83/1.07  thf(t3_xboole_0, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.83/1.07            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.83/1.07       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.83/1.07            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.83/1.07  thf('22', plain,
% 0.83/1.07      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.83/1.07         (~ (r2_hidden @ X4 @ X2)
% 0.83/1.07          | ~ (r2_hidden @ X4 @ X5)
% 0.83/1.07          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.07  thf('23', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.83/1.07         (~ (r1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.83/1.07          | ~ (r2_hidden @ X3 @ X4))),
% 0.83/1.07      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.07  thf('24', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.07         (~ (r1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.83/1.07          | ~ (r2_hidden @ X2 @ X3))),
% 0.83/1.07      inference('sup-', [status(thm)], ['14', '23'])).
% 0.83/1.07  thf('25', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.07         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.83/1.07          | ~ (r2_hidden @ X1 @ X2))),
% 0.83/1.07      inference('sup-', [status(thm)], ['13', '24'])).
% 0.83/1.07  thf('26', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['12', '25'])).
% 0.83/1.07  thf('27', plain,
% 0.83/1.07      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.83/1.07         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '26'])).
% 0.83/1.07  thf('28', plain,
% 0.83/1.07      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.83/1.07       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['3', '27'])).
% 0.83/1.07  thf('29', plain,
% 0.83/1.07      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.83/1.07       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.83/1.07      inference('split', [status(esa)], ['2'])).
% 0.83/1.07  thf(l27_zfmisc_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.83/1.07  thf('30', plain,
% 0.83/1.07      (![X32 : $i, X33 : $i]:
% 0.83/1.07         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 0.83/1.07      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.83/1.07  thf('31', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.83/1.07  thf('32', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['30', '31'])).
% 0.83/1.07  thf('33', plain,
% 0.83/1.07      (![X50 : $i, X51 : $i]:
% 0.83/1.07         (~ (r1_xboole_0 @ (k2_relat_1 @ X50) @ X51)
% 0.83/1.07          | ((k10_relat_1 @ X50 @ X51) = (k1_xboole_0))
% 0.83/1.07          | ~ (v1_relat_1 @ X50))),
% 0.83/1.07      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.83/1.07  thf('34', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.83/1.07          | ~ (v1_relat_1 @ X1)
% 0.83/1.07          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.83/1.07  thf('35', plain,
% 0.83/1.07      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.83/1.07         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.83/1.07      inference('split', [status(esa)], ['0'])).
% 0.83/1.07  thf('36', plain,
% 0.83/1.07      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.83/1.07         | ~ (v1_relat_1 @ sk_B)))
% 0.83/1.07         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.07  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('38', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.83/1.07         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.83/1.07      inference('demod', [status(thm)], ['36', '37'])).
% 0.83/1.07  thf('39', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.83/1.07         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.83/1.07      inference('split', [status(esa)], ['2'])).
% 0.83/1.07  thf('40', plain,
% 0.83/1.07      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.07         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) & 
% 0.83/1.07             ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['38', '39'])).
% 0.83/1.07  thf('41', plain,
% 0.83/1.07      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.83/1.07       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['40'])).
% 0.83/1.07  thf('42', plain, ($false),
% 0.83/1.07      inference('sat_resolution*', [status(thm)], ['1', '28', '29', '41'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
