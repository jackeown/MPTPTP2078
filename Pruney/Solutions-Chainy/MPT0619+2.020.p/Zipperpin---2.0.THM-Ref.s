%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4u9b6p1bWv

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 112 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  572 (1008 expanded)
%              Number of equality atoms :   67 ( 122 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X18 @ X23 )
      | ( X23
       != ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X18 @ ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X32 ) )
      | ( ( k11_relat_1 @ X32 @ X33 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X28: $i] :
      ( ( ( k9_relat_1 @ X28 @ ( k1_relat_1 @ X28 ) )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('23',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('27',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k11_relat_1 @ X30 @ X31 ) )
      | ( r2_hidden @ ( k4_tarski @ X31 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ X35 )
      | ( X36
        = ( k1_funct_1 @ X35 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( sk_C @ X11 @ X10 )
       != X11 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','42'])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4u9b6p1bWv
% 0.13/0.37  % Computer   : n010.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:33:45 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 55 iterations in 0.039s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.22/0.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('0', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(t70_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf(t71_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.52  thf(d2_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.52     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.22/0.52       ( ![F:$i]:
% 0.22/0.52         ( ( r2_hidden @ F @ E ) <=>
% 0.22/0.52           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.22/0.52                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.22/0.52  thf(zf_stmt_1, axiom,
% 0.22/0.52    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.52     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.22/0.52       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.22/0.52         ( ( F ) != ( D ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.52     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.22/0.52       ( ![F:$i]:
% 0.22/0.52         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.52         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.22/0.52          | (r2_hidden @ X18 @ X23)
% 0.22/0.52          | ((X23) != (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((r2_hidden @ X18 @ (k2_enumset1 @ X22 @ X21 @ X20 @ X19))
% 0.22/0.52          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.22/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.22/0.52          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12)),
% 0.22/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '8'])).
% 0.22/0.52  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['0', '9'])).
% 0.22/0.52  thf(t14_funct_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.52         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_3, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.52            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.22/0.52  thf('11', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf(t205_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.52         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X32 : $i, X33 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X33 @ (k1_relat_1 @ X32))
% 0.22/0.52          | ((k11_relat_1 @ X32 @ X33) != (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X32))),
% 0.22/0.52      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.52          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '15'])).
% 0.22/0.52  thf('17', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf(t146_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X28 : $i]:
% 0.22/0.52         (((k9_relat_1 @ X28 @ (k1_relat_1 @ X28)) = (k2_relat_1 @ X28))
% 0.22/0.52          | ~ (v1_relat_1 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf(d16_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i]:
% 0.22/0.52         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 0.22/0.52          | ~ (v1_relat_1 @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('25', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf(t41_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (((X10) = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.22/0.52          | ((X10) = (k1_tarski @ X11)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.52  thf('27', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf(t204_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ C ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X29 @ (k11_relat_1 @ X30 @ X31))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X31 @ X29) @ X30)
% 0.22/0.52          | ~ (v1_relat_1 @ X30))),
% 0.22/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '31'])).
% 0.22/0.52  thf(t8_funct_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ X35)
% 0.22/0.52          | ((X36) = (k1_funct_1 @ X35 @ X34))
% 0.22/0.52          | ~ (v1_funct_1 @ X35)
% 0.22/0.52          | ~ (v1_relat_1 @ X35))),
% 0.22/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.52          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (((X10) = (k1_xboole_0))
% 0.22/0.52          | ((sk_C @ X11 @ X10) != (X11))
% 0.22/0.52          | ((X10) = (k1_tarski @ X11)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.52          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.52        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('42', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['25', '42'])).
% 0.22/0.52  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '43'])).
% 0.22/0.52  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
