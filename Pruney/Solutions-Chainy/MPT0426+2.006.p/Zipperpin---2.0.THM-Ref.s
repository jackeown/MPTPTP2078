%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fYoMvfy8q9

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 234 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  651 (2788 expanded)
%              Number of equality atoms :   47 ( 121 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t58_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r2_hidden @ B @ A )
       => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
             => ( r2_hidden @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ C )
               => ( r2_hidden @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_setfam_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k6_setfam_1 @ X11 @ X10 )
        = ( k1_setfam_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X2 @ X1 )
        = ( k6_setfam_1 @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('12',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X18 )
      | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_B @ ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['9','15'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X3
       != ( k1_setfam_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X3 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ ( k1_setfam_1 @ X4 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X6 @ X4 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X0 )
        | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X8: $i] :
      ( ( X3
       != ( k1_setfam_1 @ X4 ) )
      | ( r2_hidden @ X8 @ X3 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X4 ) @ X4 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('34',plain,(
    ! [X4: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X4 ) @ X4 )
      | ( r2_hidden @ X8 @ ( k1_setfam_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X18: $i] :
        ( ~ ( r2_hidden @ X18 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X18 ) )
   <= ! [X18: $i] :
        ( ~ ( r2_hidden @ X18 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X18 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,
    ( ! [X18: $i] :
        ( ~ ( r2_hidden @ X18 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X18 ) )
    | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('37',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X18 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30','36'])).

thf('38',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X18 ) ) ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X8: $i] :
      ( ( X3
       != ( k1_setfam_1 @ X4 ) )
      | ( r2_hidden @ X8 @ X3 )
      | ~ ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('41',plain,(
    ! [X4: $i,X8: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X4 ) )
      | ( r2_hidden @ X8 @ ( k1_setfam_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('48',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X2 @ X1 )
        = X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('53',plain,(
    ! [X2: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X2 ) ) )
      | ( ( k8_setfam_1 @ X2 @ k1_xboole_0 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k8_setfam_1 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['32','51','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fYoMvfy8q9
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 80 iterations in 0.044s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t58_setfam_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( r2_hidden @ B @ A ) =>
% 0.20/0.49         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.20/0.49           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49          ( ( r2_hidden @ B @ A ) =>
% 0.20/0.49            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.20/0.49              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ sk_D_2)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_2 @ sk_C_1)
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_2 @ sk_C_1)) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (((k6_setfam_1 @ X11 @ X10) = (k1_setfam_1 @ X10))
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.49  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d10_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         (((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k8_setfam_1 @ X2 @ X1) = (k6_setfam_1 @ X2 @ X1))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2))))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.49        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X18 @ sk_C_1)
% 0.20/0.49          | (r2_hidden @ sk_B @ X18)
% 0.20/0.49          | (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((r2_hidden @ sk_B @ (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.49         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '15'])).
% 0.20/0.49  thf(d1_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.20/0.49         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X3) != (k1_setfam_1 @ X4))
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.49          | (r2_hidden @ X7 @ X6)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X3)
% 0.20/0.49          | ((X4) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X4) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X7 @ (k1_setfam_1 @ X4))
% 0.20/0.49          | (r2_hidden @ X7 @ X6)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ X4))),
% 0.20/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((sk_C_1) = (k1_xboole_0))
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.49           | (r2_hidden @ sk_B @ X0)
% 0.20/0.49           | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ sk_B @ X0)
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.49           | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_D_2)))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.49             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ sk_D_2)) <= (~ ((r2_hidden @ sk_B @ sk_D_2)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((((sk_C_1) = (k1_xboole_0)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.49             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.49             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_2 @ k1_xboole_0))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.49             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.49             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(t5_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.49          | ~ (v1_xboole_0 @ X17)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((![X0 : $i]: ~ (v1_xboole_0 @ X0))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.49             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.49             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_D_2 @ sk_C_1)) | ((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '29'])).
% 0.20/0.49  thf('31', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '4', '30'])).
% 0.20/0.49  thf('32', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X8 : $i]:
% 0.20/0.49         (((X3) != (k1_setfam_1 @ X4))
% 0.20/0.49          | (r2_hidden @ X8 @ X3)
% 0.20/0.49          | (r2_hidden @ (sk_D_1 @ X8 @ X4) @ X4)
% 0.20/0.49          | ((X4) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X4 : $i, X8 : $i]:
% 0.20/0.49         (((X4) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ (sk_D_1 @ X8 @ X4) @ X4)
% 0.20/0.49          | (r2_hidden @ X8 @ (k1_setfam_1 @ X4)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((![X18 : $i]: (~ (r2_hidden @ X18 @ sk_C_1) | (r2_hidden @ sk_B @ X18)))
% 0.20/0.49         <= ((![X18 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X18 @ sk_C_1) | (r2_hidden @ sk_B @ X18))))),
% 0.20/0.49      inference('split', [status(esa)], ['13'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((![X18 : $i]: (~ (r2_hidden @ X18 @ sk_C_1) | (r2_hidden @ sk_B @ X18))) | 
% 0.20/0.49       ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['13'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((![X18 : $i]: (~ (r2_hidden @ X18 @ sk_C_1) | (r2_hidden @ sk_B @ X18)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '4', '30', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X18 : $i]: (~ (r2_hidden @ X18 @ sk_C_1) | (r2_hidden @ sk_B @ X18))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ sk_B @ (sk_D_1 @ X0 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X8 : $i]:
% 0.20/0.49         (((X3) != (k1_setfam_1 @ X4))
% 0.20/0.49          | (r2_hidden @ X8 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X4))
% 0.20/0.49          | ((X4) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X4 : $i, X8 : $i]:
% 0.20/0.49         (((X4) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X4))
% 0.20/0.49          | (r2_hidden @ X8 @ (k1_setfam_1 @ X4)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.49        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.49        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((~ (r2_hidden @ sk_B @ (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.49         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '4', '30'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.49        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.49      inference('clc', [status(thm)], ['43', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         (((X1) != (k1_xboole_0))
% 0.20/0.49          | ((k8_setfam_1 @ X2 @ X1) = (X2))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2))))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X2)))
% 0.20/0.49          | ((k8_setfam_1 @ X2 @ k1_xboole_0) = (X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf('55', plain, (![X2 : $i]: ((k8_setfam_1 @ X2 @ k1_xboole_0) = (X2))),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ($false),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '51', '55', '56'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
