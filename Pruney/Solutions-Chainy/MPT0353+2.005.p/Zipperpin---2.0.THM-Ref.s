%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UgEMD5cbKL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 7.77s
% Output     : Refutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  539 (1159 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k6_subset_1 @ X37 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ( k6_subset_1 @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k9_subset_1 @ X42 @ X40 @ X41 )
        = ( k3_xboole_0 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k6_subset_1 @ X15 @ X16 ) )
      = ( k6_subset_1 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k6_subset_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['35','49'])).

thf('51',plain,(
    ( k6_subset_1 @ sk_B @ sk_C_1 )
 != ( k6_subset_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','34','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UgEMD5cbKL
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.77/7.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.77/7.95  % Solved by: fo/fo7.sh
% 7.77/7.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.77/7.95  % done 4457 iterations in 7.492s
% 7.77/7.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.77/7.95  % SZS output start Refutation
% 7.77/7.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.77/7.95  thf(sk_A_type, type, sk_A: $i).
% 7.77/7.95  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 7.77/7.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.77/7.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.77/7.95  thf(sk_B_type, type, sk_B: $i).
% 7.77/7.95  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 7.77/7.95  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.77/7.95  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.77/7.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.77/7.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.77/7.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.77/7.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.77/7.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.77/7.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.77/7.95  thf(t32_subset_1, conjecture,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95       ( ![C:$i]:
% 7.77/7.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95           ( ( k7_subset_1 @ A @ B @ C ) =
% 7.77/7.95             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 7.77/7.95  thf(zf_stmt_0, negated_conjecture,
% 7.77/7.95    (~( ![A:$i,B:$i]:
% 7.77/7.95        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95          ( ![C:$i]:
% 7.77/7.95            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95              ( ( k7_subset_1 @ A @ B @ C ) =
% 7.77/7.95                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 7.77/7.95    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 7.77/7.95  thf('0', plain,
% 7.77/7.95      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 7.77/7.95         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 7.77/7.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.77/7.95  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.77/7.95  thf(d2_subset_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( ( ( v1_xboole_0 @ A ) =>
% 7.77/7.95         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 7.77/7.95       ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.77/7.95         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 7.77/7.95  thf('2', plain,
% 7.77/7.95      (![X27 : $i, X28 : $i]:
% 7.77/7.95         (~ (m1_subset_1 @ X27 @ X28)
% 7.77/7.95          | (r2_hidden @ X27 @ X28)
% 7.77/7.95          | (v1_xboole_0 @ X28))),
% 7.77/7.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.77/7.95  thf('3', plain,
% 7.77/7.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.77/7.95        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 7.77/7.95      inference('sup-', [status(thm)], ['1', '2'])).
% 7.77/7.95  thf(fc1_subset_1, axiom,
% 7.77/7.95    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.77/7.95  thf('4', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 7.77/7.95      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.77/7.95  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('clc', [status(thm)], ['3', '4'])).
% 7.77/7.95  thf(d1_zfmisc_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 7.77/7.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 7.77/7.95  thf('6', plain,
% 7.77/7.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.77/7.95         (~ (r2_hidden @ X23 @ X22)
% 7.77/7.95          | (r1_tarski @ X23 @ X21)
% 7.77/7.95          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 7.77/7.95      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 7.77/7.95  thf('7', plain,
% 7.77/7.95      (![X21 : $i, X23 : $i]:
% 7.77/7.95         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 7.77/7.95      inference('simplify', [status(thm)], ['6'])).
% 7.77/7.95  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 7.77/7.95      inference('sup-', [status(thm)], ['5', '7'])).
% 7.77/7.95  thf(t28_xboole_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.77/7.95  thf('9', plain,
% 7.77/7.95      (![X10 : $i, X11 : $i]:
% 7.77/7.95         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 7.77/7.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.77/7.95  thf('10', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 7.77/7.95      inference('sup-', [status(thm)], ['8', '9'])).
% 7.77/7.95  thf(commutativity_k3_xboole_0, axiom,
% 7.77/7.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.77/7.95  thf('11', plain,
% 7.77/7.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.77/7.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.77/7.95  thf(t100_xboole_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.77/7.95  thf('12', plain,
% 7.77/7.95      (![X8 : $i, X9 : $i]:
% 7.77/7.95         ((k4_xboole_0 @ X8 @ X9)
% 7.77/7.95           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 7.77/7.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.77/7.95  thf(redefinition_k6_subset_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 7.77/7.95  thf('13', plain,
% 7.77/7.95      (![X35 : $i, X36 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 7.77/7.95  thf('14', plain,
% 7.77/7.95      (![X8 : $i, X9 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X8 @ X9)
% 7.77/7.95           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 7.77/7.95      inference('demod', [status(thm)], ['12', '13'])).
% 7.77/7.95  thf('15', plain,
% 7.77/7.95      (![X0 : $i, X1 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X0 @ X1)
% 7.77/7.95           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.77/7.95      inference('sup+', [status(thm)], ['11', '14'])).
% 7.77/7.95  thf('16', plain,
% 7.77/7.95      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 7.77/7.95      inference('sup+', [status(thm)], ['10', '15'])).
% 7.77/7.95  thf('17', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.77/7.95  thf(d5_subset_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.77/7.95  thf('18', plain,
% 7.77/7.95      (![X30 : $i, X31 : $i]:
% 7.77/7.95         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 7.77/7.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 7.77/7.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.77/7.95  thf('19', plain,
% 7.77/7.95      (![X35 : $i, X36 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 7.77/7.95  thf('20', plain,
% 7.77/7.95      (![X30 : $i, X31 : $i]:
% 7.77/7.95         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 7.77/7.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 7.77/7.95      inference('demod', [status(thm)], ['18', '19'])).
% 7.77/7.95  thf('21', plain,
% 7.77/7.95      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 7.77/7.95      inference('sup-', [status(thm)], ['17', '20'])).
% 7.77/7.95  thf('22', plain,
% 7.77/7.95      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 7.77/7.95      inference('sup+', [status(thm)], ['16', '21'])).
% 7.77/7.95  thf('23', plain,
% 7.77/7.95      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 7.77/7.95         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 7.77/7.95      inference('demod', [status(thm)], ['0', '22'])).
% 7.77/7.95  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.77/7.95  thf(redefinition_k7_subset_1, axiom,
% 7.77/7.95    (![A:$i,B:$i,C:$i]:
% 7.77/7.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 7.77/7.95  thf('25', plain,
% 7.77/7.95      (![X37 : $i, X38 : $i, X39 : $i]:
% 7.77/7.95         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 7.77/7.95          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.77/7.95  thf('26', plain,
% 7.77/7.95      (![X35 : $i, X36 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 7.77/7.95  thf('27', plain,
% 7.77/7.95      (![X37 : $i, X38 : $i, X39 : $i]:
% 7.77/7.95         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 7.77/7.95          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k6_subset_1 @ X37 @ X39)))),
% 7.77/7.95      inference('demod', [status(thm)], ['25', '26'])).
% 7.77/7.95  thf('28', plain,
% 7.77/7.95      (![X0 : $i]:
% 7.77/7.95         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 7.77/7.95      inference('sup-', [status(thm)], ['24', '27'])).
% 7.77/7.95  thf('29', plain,
% 7.77/7.95      (((k6_subset_1 @ sk_B @ sk_C_1)
% 7.77/7.95         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 7.77/7.95      inference('demod', [status(thm)], ['23', '28'])).
% 7.77/7.95  thf('30', plain,
% 7.77/7.95      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 7.77/7.95      inference('sup+', [status(thm)], ['10', '15'])).
% 7.77/7.95  thf(dt_k6_subset_1, axiom,
% 7.77/7.95    (![A:$i,B:$i]:
% 7.77/7.95     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 7.77/7.95  thf('31', plain,
% 7.77/7.95      (![X32 : $i, X33 : $i]:
% 7.77/7.95         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 7.77/7.95      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 7.77/7.95  thf('32', plain,
% 7.77/7.95      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('sup+', [status(thm)], ['30', '31'])).
% 7.77/7.95  thf(redefinition_k9_subset_1, axiom,
% 7.77/7.95    (![A:$i,B:$i,C:$i]:
% 7.77/7.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.77/7.95       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 7.77/7.95  thf('33', plain,
% 7.77/7.95      (![X40 : $i, X41 : $i, X42 : $i]:
% 7.77/7.95         (((k9_subset_1 @ X42 @ X40 @ X41) = (k3_xboole_0 @ X40 @ X41))
% 7.77/7.95          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 7.77/7.95  thf('34', plain,
% 7.77/7.95      (![X0 : $i]:
% 7.77/7.95         ((k9_subset_1 @ sk_A @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 7.77/7.95           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 7.77/7.95      inference('sup-', [status(thm)], ['32', '33'])).
% 7.77/7.95  thf('35', plain,
% 7.77/7.95      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 7.77/7.95      inference('sup+', [status(thm)], ['10', '15'])).
% 7.77/7.95  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.77/7.95  thf('37', plain,
% 7.77/7.95      (![X27 : $i, X28 : $i]:
% 7.77/7.95         (~ (m1_subset_1 @ X27 @ X28)
% 7.77/7.95          | (r2_hidden @ X27 @ X28)
% 7.77/7.95          | (v1_xboole_0 @ X28))),
% 7.77/7.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.77/7.95  thf('38', plain,
% 7.77/7.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.77/7.95        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 7.77/7.95      inference('sup-', [status(thm)], ['36', '37'])).
% 7.77/7.95  thf('39', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 7.77/7.95      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.77/7.95  thf('40', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.77/7.95      inference('clc', [status(thm)], ['38', '39'])).
% 7.77/7.95  thf('41', plain,
% 7.77/7.95      (![X21 : $i, X23 : $i]:
% 7.77/7.95         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 7.77/7.95      inference('simplify', [status(thm)], ['6'])).
% 7.77/7.95  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.77/7.95      inference('sup-', [status(thm)], ['40', '41'])).
% 7.77/7.95  thf('43', plain,
% 7.77/7.95      (![X10 : $i, X11 : $i]:
% 7.77/7.95         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 7.77/7.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.77/7.95  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 7.77/7.95      inference('sup-', [status(thm)], ['42', '43'])).
% 7.77/7.95  thf(t49_xboole_1, axiom,
% 7.77/7.95    (![A:$i,B:$i,C:$i]:
% 7.77/7.95     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 7.77/7.95       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 7.77/7.95  thf('45', plain,
% 7.77/7.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.77/7.95         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 7.77/7.95           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 7.77/7.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 7.77/7.95  thf('46', plain,
% 7.77/7.95      (![X35 : $i, X36 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 7.77/7.95  thf('47', plain,
% 7.77/7.95      (![X35 : $i, X36 : $i]:
% 7.77/7.95         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 7.77/7.95      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 7.77/7.95  thf('48', plain,
% 7.77/7.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.77/7.95         ((k3_xboole_0 @ X14 @ (k6_subset_1 @ X15 @ X16))
% 7.77/7.95           = (k6_subset_1 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 7.77/7.95      inference('demod', [status(thm)], ['45', '46', '47'])).
% 7.77/7.95  thf('49', plain,
% 7.77/7.95      (![X0 : $i]:
% 7.77/7.95         ((k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ X0))
% 7.77/7.95           = (k6_subset_1 @ sk_B @ X0))),
% 7.77/7.95      inference('sup+', [status(thm)], ['44', '48'])).
% 7.77/7.95  thf('50', plain,
% 7.77/7.95      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 7.77/7.95         = (k6_subset_1 @ sk_B @ sk_C_1))),
% 7.77/7.95      inference('sup+', [status(thm)], ['35', '49'])).
% 7.77/7.95  thf('51', plain,
% 7.77/7.95      (((k6_subset_1 @ sk_B @ sk_C_1) != (k6_subset_1 @ sk_B @ sk_C_1))),
% 7.77/7.95      inference('demod', [status(thm)], ['29', '34', '50'])).
% 7.77/7.95  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 7.77/7.95  
% 7.77/7.95  % SZS output end Refutation
% 7.77/7.95  
% 7.79/7.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
