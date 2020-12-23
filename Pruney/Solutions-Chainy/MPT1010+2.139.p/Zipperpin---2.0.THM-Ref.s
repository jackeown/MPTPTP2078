%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxi3jprJKQ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  75 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  431 ( 613 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ( X60 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_funct_2 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X61 @ X58 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50 != X49 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X49 ) )
       != ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X49: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X49 ) @ ( k1_tarski @ X49 ) )
     != ( k1_tarski @ X49 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('13',plain,(
    ! [X52: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X52 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['12','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['6','27'])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('31',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxi3jprJKQ
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 327 iterations in 0.128s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(t65_funct_2, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.58            ( m1_subset_1 @
% 0.21/0.58              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.58          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.58  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t7_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X58 @ X59)
% 0.21/0.58          | ((X60) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_funct_1 @ X61)
% 0.21/0.58          | ~ (v1_funct_2 @ X61 @ X59 @ X60)
% 0.21/0.58          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 0.21/0.58          | (r2_hidden @ (k1_funct_1 @ X61 @ X58) @ X60))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.21/0.58          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.21/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.58          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.21/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.21/0.58          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.21/0.58          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.58  thf(t69_enumset1, axiom,
% 0.21/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.58  thf('7', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf('8', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf(t20_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.58         ( k1_tarski @ A ) ) <=>
% 0.21/0.58       ( ( A ) != ( B ) ) ))).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X49 : $i, X50 : $i]:
% 0.21/0.58         (((X50) != (X49))
% 0.21/0.58          | ((k4_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X49))
% 0.21/0.58              != (k1_tarski @ X50)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X49 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ (k1_tarski @ X49) @ (k1_tarski @ X49))
% 0.21/0.58           != (k1_tarski @ X49))),
% 0.21/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.21/0.58           != (k1_tarski @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0))
% 0.21/0.58           != (k1_tarski @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.58  thf(t6_mcart_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.58                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.58                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.58                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.58                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.58                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X52 : $i]:
% 0.21/0.58         (((X52) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X52) @ X52))),
% 0.21/0.58      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.58  thf(t3_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('14', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf(t48_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.58           = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf(d4_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.58          | (r2_hidden @ X4 @ X2)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.21/0.58          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.58  thf(t5_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('20', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.58  thf(t1_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.58       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.58          | ~ (r2_hidden @ X6 @ X8)
% 0.21/0.58          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.58          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.21/0.58          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.58  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.58      inference('condensation', [status(thm)], ['23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.58      inference('clc', [status(thm)], ['19', '24'])).
% 0.21/0.58  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['13', '25'])).
% 0.21/0.58  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['12', '26'])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1)))),
% 0.21/0.58      inference('clc', [status(thm)], ['6', '27'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '28'])).
% 0.21/0.58  thf(d1_tarski, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X19 @ X18)
% 0.21/0.58          | ((X19) = (X16))
% 0.21/0.58          | ((X18) != (k1_tarski @ X16)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X16 : $i, X19 : $i]:
% 0.21/0.58         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.58  thf('32', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.58  thf('33', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('34', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
