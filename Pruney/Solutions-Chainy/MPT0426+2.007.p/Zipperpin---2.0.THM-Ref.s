%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.merj8RBGZ1

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 373 expanded)
%              Number of leaves         :   20 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  621 (4629 expanded)
%              Number of equality atoms :   52 ( 240 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X5 @ X4 )
        = ( k6_setfam_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('8',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k6_setfam_1 @ sk_A @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k6_setfam_1 @ X14 @ X13 )
        = ( k1_setfam_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('11',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_1 )
    = ( k1_setfam_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X15 )
      | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

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

thf('16',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X6
       != ( k1_setfam_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X6 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('17',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r2_hidden @ X10 @ ( k1_setfam_1 @ X7 ) )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X9 @ X7 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X0 )
        | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( sk_C_1 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('23',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ sk_C_1 )
      = sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X3 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('25',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X11: $i] :
      ( ( X6
       != ( k1_setfam_1 @ X7 ) )
      | ( r2_hidden @ X11 @ X6 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X7 ) @ X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('32',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X7 ) @ X7 )
      | ( r2_hidden @ X11 @ ( k1_setfam_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X15 ) )
   <= ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X15 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('34',plain,
    ( ! [X15: $i] :
        ( ~ ( r2_hidden @ X15 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X15 ) )
    | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('35',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X15 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','28','34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X15 ) ) ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X11: $i] :
      ( ( X6
       != ( k1_setfam_1 @ X7 ) )
      | ( r2_hidden @ X11 @ X6 )
      | ~ ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X7 ) )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('39',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X7 ) )
      | ( r2_hidden @ X11 @ ( k1_setfam_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','28'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','46'])).

thf('51',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X5 @ X4 )
        = X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('53',plain,(
    ! [X5: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( ( k8_setfam_1 @ X5 @ k1_xboole_0 )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['48','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.merj8RBGZ1
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 171 iterations in 0.120s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.21/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.57  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(t58_setfam_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( ( r2_hidden @ B @ A ) =>
% 0.21/0.57         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.21/0.57           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57          ( ( r2_hidden @ B @ A ) =>
% 0.21/0.57            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.21/0.57              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ sk_D_2)
% 0.21/0.57        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.21/0.57         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.21/0.57       ~ ((r2_hidden @ sk_B @ sk_D_2))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (((r2_hidden @ sk_D_2 @ sk_C_1)
% 0.21/0.57        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (((r2_hidden @ sk_D_2 @ sk_C_1)) | 
% 0.21/0.57       ~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['3'])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['3'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d10_setfam_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.21/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (((X4) = (k1_xboole_0))
% 0.21/0.57          | ((k8_setfam_1 @ X5 @ X4) = (k6_setfam_1 @ X5 @ X4))
% 0.21/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k6_setfam_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         (((k6_setfam_1 @ X14 @ X13) = (k1_setfam_1 @ X13))
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.21/0.57  thf('11', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X15 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X15 @ sk_C_1)
% 0.21/0.57          | (r2_hidden @ sk_B @ X15)
% 0.21/0.57          | (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('split', [status(esa)], ['13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '14'])).
% 0.21/0.57  thf(d1_setfam_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.57       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.57         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.57               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (((X6) != (k1_setfam_1 @ X7))
% 0.21/0.57          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.57          | (r2_hidden @ X10 @ X9)
% 0.21/0.57          | ~ (r2_hidden @ X10 @ X6)
% 0.21/0.57          | ((X7) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (((X7) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_hidden @ X10 @ (k1_setfam_1 @ X7))
% 0.21/0.57          | (r2_hidden @ X10 @ X9)
% 0.21/0.57          | ~ (r2_hidden @ X9 @ X7))),
% 0.21/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (((sk_C_1) = (k1_xboole_0))
% 0.21/0.57           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.57           | (r2_hidden @ sk_B @ X0)
% 0.21/0.57           | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r2_hidden @ sk_B @ X0)
% 0.21/0.57           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.57           | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_D_2)))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.21/0.57             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['3'])).
% 0.21/0.57  thf(l22_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.57       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((k2_xboole_0 @ (k1_tarski @ X1) @ X0) = (X0))
% 0.21/0.57          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      ((((k2_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_C_1) = (sk_C_1)))
% 0.21/0.57         <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf(t49_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ (k1_tarski @ X2) @ X3) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      ((((sk_C_1) != (k1_xboole_0))) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ sk_D_2))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.21/0.57             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['20', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ sk_D_2)) <= (~ ((r2_hidden @ sk_B @ sk_D_2)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.21/0.57       ~ ((r2_hidden @ sk_D_2 @ sk_C_1)) | ((r2_hidden @ sk_B @ sk_D_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['2', '4', '28'])).
% 0.21/0.57  thf('30', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X11 : $i]:
% 0.21/0.57         (((X6) != (k1_setfam_1 @ X7))
% 0.21/0.57          | (r2_hidden @ X11 @ X6)
% 0.21/0.57          | (r2_hidden @ (sk_D_1 @ X11 @ X7) @ X7)
% 0.21/0.57          | ((X7) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X7 : $i, X11 : $i]:
% 0.21/0.57         (((X7) = (k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ (sk_D_1 @ X11 @ X7) @ X7)
% 0.21/0.57          | (r2_hidden @ X11 @ (k1_setfam_1 @ X7)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((![X15 : $i]: (~ (r2_hidden @ X15 @ sk_C_1) | (r2_hidden @ sk_B @ X15)))
% 0.21/0.57         <= ((![X15 : $i]:
% 0.21/0.57                (~ (r2_hidden @ X15 @ sk_C_1) | (r2_hidden @ sk_B @ X15))))),
% 0.21/0.57      inference('split', [status(esa)], ['13'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((![X15 : $i]: (~ (r2_hidden @ X15 @ sk_C_1) | (r2_hidden @ sk_B @ X15))) | 
% 0.21/0.57       ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['13'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((![X15 : $i]: (~ (r2_hidden @ X15 @ sk_C_1) | (r2_hidden @ sk_B @ X15)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['2', '4', '28', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X15 : $i]: (~ (r2_hidden @ X15 @ sk_C_1) | (r2_hidden @ sk_B @ X15))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57          | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ sk_B @ (sk_D_1 @ X0 @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X11 : $i]:
% 0.21/0.57         (((X6) != (k1_setfam_1 @ X7))
% 0.21/0.57          | (r2_hidden @ X11 @ X6)
% 0.21/0.57          | ~ (r2_hidden @ X11 @ (sk_D_1 @ X11 @ X7))
% 0.21/0.57          | ((X7) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X7 : $i, X11 : $i]:
% 0.21/0.57         (((X7) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_hidden @ X11 @ (sk_D_1 @ X11 @ X7))
% 0.21/0.57          | (r2_hidden @ X11 @ (k1_setfam_1 @ X7)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.57        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.21/0.57         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('45', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['2', '4', '28'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.21/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['41', '46'])).
% 0.21/0.57  thf('48', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['30', '47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['41', '46'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (((X4) != (k1_xboole_0))
% 0.21/0.57          | ((k8_setfam_1 @ X5 @ X4) = (X5))
% 0.21/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X5 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.21/0.57          | ((k8_setfam_1 @ X5 @ k1_xboole_0) = (X5)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.57  thf('54', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '53'])).
% 0.21/0.57  thf('55', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('56', plain, ($false),
% 0.21/0.57      inference('demod', [status(thm)], ['48', '54', '55'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
