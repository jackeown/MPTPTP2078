%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zSqtfjLnQp

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:35 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 150 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  693 (2249 expanded)
%              Number of equality atoms :   93 ( 345 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X33
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X30 @ X31 @ X32 @ X33 ) @ ( k6_mcart_1 @ X30 @ X31 @ X32 @ X33 ) @ ( k7_mcart_1 @ X30 @ X31 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('7',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ( ( sk_B @ X26 )
       != ( k3_mcart_1 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['21'])).

thf('24',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('25',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k2_mcart_1 @ X17 ) )
      | ( X17
       != ( k4_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_tarski @ X18 @ X19 )
     != ( k2_mcart_1 @ ( k4_tarski @ X18 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('29',plain,(
    ! [X34: $i,X36: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X34 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_tarski @ X18 @ X19 )
     != X19 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['21'])).

thf('34',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ( ( sk_B @ X26 )
       != ( k3_mcart_1 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['42','44'])).

thf('46',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['21'])).

thf('47',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['32','45','46'])).

thf('48',plain,
    ( sk_D
    = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['20','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zSqtfjLnQp
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 121 iterations in 0.089s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.54  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.37/0.54  thf(t51_mcart_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ~( ![D:$i]:
% 0.37/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.54                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.37/0.54                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.37/0.54                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54             ( ~( ![D:$i]:
% 0.37/0.54                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.54                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.37/0.54                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.37/0.54                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t48_mcart_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ~( ![D:$i]:
% 0.37/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.54                 ( ( D ) =
% 0.37/0.54                   ( k3_mcart_1 @
% 0.37/0.54                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.37/0.54                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.37/0.54                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.54         (((X30) = (k1_xboole_0))
% 0.37/0.54          | ((X31) = (k1_xboole_0))
% 0.37/0.54          | ((X33)
% 0.37/0.54              = (k3_mcart_1 @ (k5_mcart_1 @ X30 @ X31 @ X32 @ X33) @ 
% 0.37/0.54                 (k6_mcart_1 @ X30 @ X31 @ X32 @ X33) @ 
% 0.37/0.54                 (k7_mcart_1 @ X30 @ X31 @ X32 @ X33)))
% 0.37/0.54          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X30 @ X31 @ X32))
% 0.37/0.54          | ((X32) = (k1_xboole_0)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      ((((sk_C_1) = (k1_xboole_0))
% 0.37/0.54        | ((sk_D)
% 0.37/0.54            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.37/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('4', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('5', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (((sk_D)
% 0.37/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.37/0.54  thf(t29_mcart_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ![B:$i]:
% 0.37/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.54                 ( ![C:$i,D:$i,E:$i]:
% 0.37/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.37/0.54                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X26 : $i]:
% 0.37/0.54         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.37/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.37/0.54  thf(d1_tarski, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X1 : $i, X4 : $i]:
% 0.37/0.54         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.54          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.54  thf(idempotence_k2_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.54  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.54  thf(t49_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.37/0.54  thf('13', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('14', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.54         (((X26) = (k1_xboole_0))
% 0.37/0.54          | ~ (r2_hidden @ X28 @ X26)
% 0.37/0.54          | ((sk_B @ X26) != (k3_mcart_1 @ X28 @ X27 @ X29)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.37/0.54          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.37/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.37/0.54          | ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.54  thf('18', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54          (k1_tarski @ sk_D))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.37/0.54        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.37/0.54        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.37/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.37/0.54      inference('split', [status(esa)], ['21'])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.37/0.54         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.37/0.54      inference('split', [status(esa)], ['21'])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (((sk_D)
% 0.37/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      ((((sk_D)
% 0.37/0.54          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_D)))
% 0.37/0.54         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.37/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.54  thf(d3_mcart_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.54         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 0.37/0.54           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.37/0.54  thf(t20_mcart_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.54       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         (((X17) != (k2_mcart_1 @ X17)) | ((X17) != (k4_tarski @ X18 @ X19)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         ((k4_tarski @ X18 @ X19) != (k2_mcart_1 @ (k4_tarski @ X18 @ X19)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.54  thf(t7_mcart_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.37/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X34 : $i, X36 : $i]: ((k2_mcart_1 @ (k4_tarski @ X34 @ X36)) = (X36))),
% 0.37/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.54  thf('30', plain, (![X18 : $i, X19 : $i]: ((k4_tarski @ X18 @ X19) != (X19))),
% 0.37/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['26', '30'])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['25', '31'])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.37/0.54         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.37/0.54      inference('split', [status(esa)], ['21'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (((sk_D)
% 0.37/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.37/0.54  thf('35', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.54         (((X26) = (k1_xboole_0))
% 0.37/0.54          | ~ (r2_hidden @ X27 @ X26)
% 0.37/0.54          | ((sk_B @ X26) != (k3_mcart_1 @ X28 @ X27 @ X29)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.37/0.54          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.37/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.37/0.54          | ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.37/0.54  thf('39', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.37/0.54  thf('41', plain,
% 0.37/0.54      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.37/0.54          (k1_tarski @ sk_D))),
% 0.37/0.54      inference('sup-', [status(thm)], ['34', '40'])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))
% 0.37/0.54         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '41'])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.54  thf('44', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.37/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      (~ (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('demod', [status(thm)], ['42', '44'])).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.37/0.54       (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.37/0.54       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('split', [status(esa)], ['21'])).
% 0.37/0.54  thf('47', plain, ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['32', '45', '46'])).
% 0.37/0.54  thf('48', plain, (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['22', '47'])).
% 0.37/0.54  thf('49', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.37/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.54  thf('50', plain, ($false),
% 0.37/0.54      inference('demod', [status(thm)], ['20', '48', '49'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
