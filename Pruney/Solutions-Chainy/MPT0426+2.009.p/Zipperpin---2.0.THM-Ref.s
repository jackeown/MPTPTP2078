%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eht4zDl9BV

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 226 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  611 (2712 expanded)
%              Number of equality atoms :   51 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

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
    ( ( r2_hidden @ sk_D_2 @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

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
    ! [X7: $i,X8: $i,X12: $i] :
      ( ( X7
       != ( k1_setfam_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X8 ) @ X8 )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('32',plain,(
    ! [X8: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X8 ) @ X8 )
      | ( r2_hidden @ X12 @ ( k1_setfam_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X19: $i] :
        ( ~ ( r2_hidden @ X19 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X19 ) )
   <= ! [X19: $i] :
        ( ~ ( r2_hidden @ X19 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X19 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('34',plain,
    ( ! [X19: $i] :
        ( ~ ( r2_hidden @ X19 @ sk_C_1 )
        | ( r2_hidden @ sk_B @ X19 ) )
    | ( r2_hidden @ sk_B @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('35',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','28','34'])).

thf('36',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ X19 ) ) ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_1 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X12: $i] :
      ( ( X7
       != ( k1_setfam_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X7 )
      | ~ ( r2_hidden @ X12 @ ( sk_D_1 @ X12 @ X8 ) )
      | ( X8 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('39',plain,(
    ! [X8: $i,X12: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ ( sk_D_1 @ X12 @ X8 ) )
      | ( r2_hidden @ X12 @ ( k1_setfam_1 @ X8 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( X5 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X6 @ X5 )
        = X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('49',plain,(
    ! [X6: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) )
      | ( ( k8_setfam_1 @ X6 @ k1_xboole_0 )
        = X6 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X6: $i] :
      ( ( k8_setfam_1 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['30','47','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eht4zDl9BV
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 155 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(t58_setfam_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( r2_hidden @ B @ A ) =>
% 0.20/0.52         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.20/0.52           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52          ( ( r2_hidden @ B @ A ) =>
% 0.20/0.52            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 0.20/0.52              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ sk_D_2)
% 0.20/0.52        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ sk_C_1)
% 0.20/0.52        | ~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ sk_C_1)) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d10_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         (((X5) = (k1_xboole_0))
% 0.20/0.52          | ((k8_setfam_1 @ X6 @ X5) = (k6_setfam_1 @ X6 @ X5))
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k6_setfam_1 @ sk_A @ sk_C_1))
% 0.20/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         (((k6_setfam_1 @ X15 @ X14) = (k1_setfam_1 @ X14))
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.52  thf('11', plain, (((k6_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.20/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X19 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X19 @ sk_C_1)
% 0.20/0.52          | (r2_hidden @ sk_B @ X19)
% 0.20/0.52          | (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.52  thf(d1_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.20/0.52         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.52         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.52               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.52          | ~ (r2_hidden @ X10 @ X8)
% 0.20/0.52          | (r2_hidden @ X11 @ X10)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ X7)
% 0.20/0.52          | ((X8) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (((X8) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X11 @ (k1_setfam_1 @ X8))
% 0.20/0.52          | (r2_hidden @ X11 @ X10)
% 0.20/0.52          | ~ (r2_hidden @ X10 @ X8))),
% 0.20/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (((sk_C_1) = (k1_xboole_0))
% 0.20/0.52           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.52           | (r2_hidden @ sk_B @ X0)
% 0.20/0.52           | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ sk_B @ X0)
% 0.20/0.52           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.52           | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_B @ sk_D_2)))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.52             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ sk_C_1)) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf(t46_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k2_xboole_0 @ (k1_tarski @ X1) @ X0) = (X0))
% 0.20/0.52          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((((k2_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_C_1) = (sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf(t49_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k1_tarski @ X2) @ X3) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((sk_C_1) != (k1_xboole_0))) <= (((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ sk_D_2))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) & 
% 0.20/0.52             ((r2_hidden @ sk_D_2 @ sk_C_1)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['20', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ sk_D_2)) <= (~ ((r2_hidden @ sk_B @ sk_D_2)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_D_2 @ sk_C_1)) | ((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '4', '28'])).
% 0.20/0.52  thf('30', plain, (~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X12 : $i]:
% 0.20/0.52         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.52          | (r2_hidden @ X12 @ X7)
% 0.20/0.52          | (r2_hidden @ (sk_D_1 @ X12 @ X8) @ X8)
% 0.20/0.52          | ((X8) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X8 : $i, X12 : $i]:
% 0.20/0.52         (((X8) = (k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ (sk_D_1 @ X12 @ X8) @ X8)
% 0.20/0.52          | (r2_hidden @ X12 @ (k1_setfam_1 @ X8)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19)))
% 0.20/0.52         <= ((![X19 : $i]:
% 0.20/0.52                (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19))))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19))) | 
% 0.20/0.52       ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '4', '28', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X19 : $i]: (~ (r2_hidden @ X19 @ sk_C_1) | (r2_hidden @ sk_B @ X19))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ sk_B @ (sk_D_1 @ X0 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X12 : $i]:
% 0.20/0.52         (((X7) != (k1_setfam_1 @ X8))
% 0.20/0.52          | (r2_hidden @ X12 @ X7)
% 0.20/0.52          | ~ (r2_hidden @ X12 @ (sk_D_1 @ X12 @ X8))
% 0.20/0.52          | ((X8) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X8 : $i, X12 : $i]:
% 0.20/0.52         (((X8) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X12 @ (sk_D_1 @ X12 @ X8))
% 0.20/0.52          | (r2_hidden @ X12 @ (k1_setfam_1 @ X8)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.52        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52        | (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((((k8_setfam_1 @ sk_A @ sk_C_1) = (k1_setfam_1 @ sk_C_1))
% 0.20/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, (~ ((r2_hidden @ sk_B @ (k8_setfam_1 @ sk_A @ sk_C_1)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '4', '28'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ (k1_setfam_1 @ sk_C_1))
% 0.20/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.52      inference('clc', [status(thm)], ['41', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         (((X5) != (k1_xboole_0))
% 0.20/0.52          | ((k8_setfam_1 @ X6 @ X5) = (X6))
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X6 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6)))
% 0.20/0.52          | ((k8_setfam_1 @ X6 @ k1_xboole_0) = (X6)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf(t4_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.52  thf('51', plain, (![X6 : $i]: ((k8_setfam_1 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('53', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '47', '51', '52'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
