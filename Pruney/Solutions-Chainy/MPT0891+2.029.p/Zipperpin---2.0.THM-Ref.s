%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DwW4qKpgRU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 200 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  761 (3774 expanded)
%              Number of equality atoms :   94 ( 584 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X17
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ ( k6_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ ( k7_mcart_1 @ X14 @ X15 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('5',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13'])).

thf(t39_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k3_zfmisc_1 @ X20 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

thf('26',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['23'])).

thf('27',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13'])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k3_zfmisc_1 @ X19 @ X20 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ ( k2_mcart_1 @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k1_tarski @ X5 ) )
      | ( X4
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('37',plain,(
    ! [X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('39',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['23'])).

thf('40',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13'])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('49',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['23'])).

thf('51',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['38','49','50'])).

thf('52',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['24','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['22','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DwW4qKpgRU
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 44 iterations in 0.015s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.49  thf(t51_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.49                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.49                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49             ( ~( ![D:$i]:
% 0.21/0.49                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.49                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.49                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.21/0.49  thf('0', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t48_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49                 ( ( D ) =
% 0.21/0.49                   ( k3_mcart_1 @
% 0.21/0.49                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.49                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.49                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (((X14) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0))
% 0.21/0.49          | ((X17)
% 0.21/0.49              = (k3_mcart_1 @ (k5_mcart_1 @ X14 @ X15 @ X16 @ X17) @ 
% 0.21/0.49                 (k6_mcart_1 @ X14 @ X15 @ X16 @ X17) @ 
% 0.21/0.49                 (k7_mcart_1 @ X14 @ X15 @ X16 @ X17)))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16))
% 0.21/0.49          | ((X16) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_D)
% 0.21/0.49            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.49               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.49               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t50_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ![D:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.49                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.49                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.49                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.49         (((X21) = (k1_xboole_0))
% 0.21/0.49          | ((X22) = (k1_xboole_0))
% 0.21/0.49          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.21/0.49          | ((X24) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_D)
% 0.21/0.49            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.49               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '9'])).
% 0.21/0.49  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((sk_D)
% 0.21/0.49         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.49            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.49  thf(t39_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_zfmisc_1 @
% 0.21/0.49         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.21/0.49       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X12) @ 
% 0.21/0.49           (k1_tarski @ X13)) = (k1_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t39_mcart_1])).
% 0.21/0.49  thf(t49_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 0.21/0.49            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 0.21/0.49            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 0.21/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (((X18) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X18 @ (k3_zfmisc_1 @ X20 @ X18 @ X19)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_tarski @ X1) @ 
% 0.21/0.49             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.21/0.49          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf(t1_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.49  thf(t49_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.49  thf('20', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ~ (r1_tarski @ (k1_tarski @ X1) @ 
% 0.21/0.49            (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['17', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (~ (r1_tarski @ (k1_tarski @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.21/0.49          (k1_tarski @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.21/0.49        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.21/0.49        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.49         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.49         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.21/0.49         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((sk_D)
% 0.21/0.49         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.49            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X12) @ 
% 0.21/0.49           (k1_tarski @ X13)) = (k1_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t39_mcart_1])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (((X18) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X18 @ (k3_zfmisc_1 @ X19 @ X20 @ X18)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_tarski @ X0) @ 
% 0.21/0.49             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.21/0.49          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ~ (r1_tarski @ (k1_tarski @ X0) @ 
% 0.21/0.49            (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (~ (r1_tarski @ (k1_tarski @ (k2_mcart_1 @ sk_D)) @ (k1_tarski @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k1_tarski @ sk_D) @ (k1_tarski @ sk_D)))
% 0.21/0.49         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '34'])).
% 0.21/0.49  thf(t39_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((r1_tarski @ X4 @ (k1_tarski @ X5)) | ((X4) != (k1_tarski @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X5 : $i]: (r1_tarski @ (k1_tarski @ X5) @ (k1_tarski @ X5))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('38', plain, (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.49         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((sk_D)
% 0.21/0.49         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.49            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11', '12', '13'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X12) @ 
% 0.21/0.49           (k1_tarski @ X13)) = (k1_tarski @ (k3_mcart_1 @ X11 @ X12 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t39_mcart_1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (((X18) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X18 @ (k3_zfmisc_1 @ X18 @ X19 @ X20)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_mcart_1])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_tarski @ X2) @ 
% 0.21/0.49             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.21/0.49          | ((k1_tarski @ X2) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ~ (r1_tarski @ (k1_tarski @ X2) @ 
% 0.21/0.49            (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (~ (r1_tarski @ (k1_tarski @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.21/0.49          (k1_tarski @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k1_tarski @ sk_D) @ (k1_tarski @ sk_D)))
% 0.21/0.49         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X5 : $i]: (r1_tarski @ (k1_tarski @ X5) @ (k1_tarski @ X5))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('49', plain, (~ (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.21/0.49       (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.21/0.49       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('51', plain, ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['38', '49', '50'])).
% 0.21/0.49  thf('52', plain, (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['24', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X5 : $i]: (r1_tarski @ (k1_tarski @ X5) @ (k1_tarski @ X5))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('54', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '52', '53'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
