%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IE2yoQpcCa

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 229 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  620 (2739 expanded)
%              Number of equality atoms :   51 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X6 @ X5 )
        = ( k6_setfam_1 @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( ( k6_setfam_1 @ X15 @ X14 )
        = ( k1_setfam_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
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
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X19 )
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
    ! [X7: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X7
       != ( k1_setfam_1 @ X8 ) )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X7 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('17',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r2_hidden @ X11 @ ( k1_setfam_1 @ X8 ) )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X10 @ X8 ) ) ),
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
    ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('24',plain,
    ( ( r2_hidden @ sk_D_2 @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
       != X2 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_2 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X12: $i] :
      ( ( X7
       != ( k1_setfam_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X8 ) @ X8 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('33',plain,(
    ! [X8: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X8 ) @ X8 )
      | ( r2_hidden @ X12 @ ( k1_setfam_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X19: $i] :
        ( ~ ( r2_hidden @ X19 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X19 ) )
   <= ! [X19: $i] :
        ( ~ ( r2_hidden @ X19 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X19 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('35',plain,
    ( ! [X19: $i] :
        ( ~ ( r2_hidden @ X19 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X19 ) )
    | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','29','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X19 ) ) ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X12: $i] :
      ( ( X7
       != ( k1_setfam_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X7 )
      | ~ ( r2_hidden @ X12 @ ( sk_D_1 @ X12 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('40',plain,(
    ! [X8: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ ( sk_D_1 @ X12 @ X8 ) )
      | ( r2_hidden @ X12 @ ( k1_setfam_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_1 )
      = ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','29'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_setfam_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X6 @ X5 )
        = X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('50',plain,(
    ! [X6: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) )
      | ( ( k8_setfam_1 @ X6 @ k1_xboole_0 )
        = X6 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('51',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( k8_setfam_1 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['31','48','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IE2yoQpcCa
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 96 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.51  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(t58_setfam_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ B @ A ) =>
% 0.20/0.51         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.20/0.51           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51          ( ( r2_hidden @ B @ A ) =>
% 0.20/0.51            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.20/0.51              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_D_2)
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ sk_C_1)
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ sk_C_1)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d10_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((X5) = (k1_xboole_0))
% 0.20/0.51          | ((k8_setfam_1 @ X6 @ X5) = (k6_setfam_1 @ X6 @ X5))
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.51  thf('11', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X19 @ sk_C_1)
% 0.20/0.51          | (r2_hidden @ sk_B @ X19)
% 0.20/0.51          | (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.51  thf(d1_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.20/0.51         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.51          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.51          | (r2_hidden @ X11 @ X10)
% 0.20/0.51          | ~ (r2_hidden @ X11 @ X7)
% 0.20/0.51          | ((X8) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (((X8) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X11 @ (k1_setfam_1 @ X8))
% 0.20/0.51          | (r2_hidden @ X11 @ X10)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ X8))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((sk_C_1) = (k1_xboole_0))
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.51           | (r2_hidden @ sk_B @ X0)
% 0.20/0.51           | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((r2_hidden @ sk_B @ X0)
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.51           | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_D_2)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.51             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_D_2)) <= (~ ((r2_hidden @ sk_B @ sk_D_2)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((((sk_C_1) = (k1_xboole_0)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.51             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.51             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ k1_xboole_0))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.51             ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.51             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf(t4_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.51  thf(t65_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.51       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ X2)
% 0.20/0.51          | ((k4_xboole_0 @ X2 @ (k1_tarski @ X1)) != (X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_D_2 @ sk_C_1)) | ((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '28'])).
% 0.20/0.51  thf('30', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '4', '29'])).
% 0.20/0.51  thf('31', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X12 : $i]:
% 0.20/0.51         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.51          | (r2_hidden @ X12 @ X7)
% 0.20/0.51          | (r2_hidden @ (sk_D_1 @ X12 @ X8) @ X8)
% 0.20/0.51          | ((X8) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X8 : $i, X12 : $i]:
% 0.20/0.51         (((X8) = (k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ (sk_D_1 @ X12 @ X8) @ X8)
% 0.20/0.51          | (r2_hidden @ X12 @ (k1_setfam_1 @ X8)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19)))
% 0.20/0.51         <= ((![X19 : $i]:
% 0.20/0.51                (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19))))),
% 0.20/0.51      inference('split', [status(esa)], ['13'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19))) | 
% 0.20/0.51       ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['13'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '4', '29', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ sk_B @ (sk_D_1 @ X0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X12 : $i]:
% 0.20/0.51         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.51          | (r2_hidden @ X12 @ X7)
% 0.20/0.51          | ~ (r2_hidden @ X12 @ (sk_D_1 @ X12 @ X8))
% 0.20/0.51          | ((X8) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X8 : $i, X12 : $i]:
% 0.20/0.51         (((X8) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X12 @ (sk_D_1 @ X12 @ X8))
% 0.20/0.51          | (r2_hidden @ X12 @ (k1_setfam_1 @ X8)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.51        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '4', '29'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.51      inference('clc', [status(thm)], ['42', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((X5) != (k1_xboole_0))
% 0.20/0.51          | ((k8_setfam_1 @ X6 @ X5) = (X6))
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X6 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6)))
% 0.20/0.51          | ((k8_setfam_1 @ X6 @ k1_xboole_0) = (X6)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.51  thf(t4_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.51  thf('52', plain, (![X6 : $i]: ((k8_setfam_1 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, ($false),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '48', '52', '53'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
