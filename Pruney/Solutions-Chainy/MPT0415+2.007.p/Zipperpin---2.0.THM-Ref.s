%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v7gambpY21

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  567 ( 929 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_setfam_1 @ X19 @ ( k7_setfam_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('3',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['3','4'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( X12
       != ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_setfam_1 @ X19 @ ( k7_setfam_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( X12
       != ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ X15 @ X12 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ( r2_hidden @ X15 @ ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('32',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ k1_xboole_0 )
    | ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v7gambpY21
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 157 iterations in 0.116s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(d3_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf(t46_setfam_1, conjecture,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.57            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i]:
% 0.37/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.57               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(involutiveness_k7_setfam_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]:
% 0.37/0.57         (((k7_setfam_1 @ X19 @ (k7_setfam_1 @ X19 @ X18)) = (X18))
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.37/0.57      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf('4', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('5', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf(d8_setfam_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57       ( ![C:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.37/0.57             ( ![D:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57                 ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.57                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.37/0.57          | ((X12) != (k7_setfam_1 @ X13 @ X14))
% 0.37/0.57          | (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.37/0.57          | ~ (r2_hidden @ X15 @ X12)
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.37/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.37/0.57      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.37/0.57          | ~ (r2_hidden @ X15 @ (k7_setfam_1 @ X13 @ X14))
% 0.37/0.57          | (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.37/0.57          | ~ (m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.37/0.57          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.37/0.57          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.57          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('10', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.57  thf(t4_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t4_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X23 @ X24)
% 0.37/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.37/0.57          | (m1_subset_1 @ X23 @ X25))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.57          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0))),
% 0.37/0.57      inference('clc', [status(thm)], ['12', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.37/0.57             k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf(t3_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.57  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X2)
% 0.37/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '22'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]:
% 0.37/0.57         (((k7_setfam_1 @ X19 @ (k7_setfam_1 @ X19 @ X18)) = (X18))
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.37/0.57      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.37/0.57          | ((X12) != (k7_setfam_1 @ X13 @ X14))
% 0.37/0.57          | (r2_hidden @ X15 @ X12)
% 0.37/0.57          | ~ (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.37/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.37/0.57      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.37/0.57          | ~ (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.37/0.57          | (r2_hidden @ X15 @ (k7_setfam_1 @ X13 @ X14))
% 0.37/0.57          | ~ (m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.37/0.57          | (r2_hidden @ X1 @ 
% 0.37/0.57             (k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))
% 0.37/0.57          | ~ (r2_hidden @ (k3_subset_1 @ X0 @ X1) @ 
% 0.37/0.57               (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.57          | ~ (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.57  thf(dt_k7_setfam_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57       ( m1_subset_1 @
% 0.37/0.57         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (k7_setfam_1 @ X16 @ X17) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.37/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.37/0.57          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ X1 @ k1_xboole_0)
% 0.37/0.57          | ~ (r2_hidden @ (k3_subset_1 @ X0 @ X1) @ 
% 0.37/0.57               (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.57      inference('demod', [status(thm)], ['29', '30', '31', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['23', '35'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0)
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ k1_xboole_0)
% 0.37/0.57          | (r1_tarski @ sk_B @ X0))),
% 0.37/0.57      inference('clc', [status(thm)], ['36', '39'])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (((r1_tarski @ sk_B @ k1_xboole_0) | (r1_tarski @ sk_B @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('43', plain, ((r1_tarski @ sk_B @ k1_xboole_0)),
% 0.37/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.57  thf(t3_xboole_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.37/0.57  thf('45', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain, ($false),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
