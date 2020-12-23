%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LgjFVBmiqZ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 6.64s
% Output     : Refutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  539 (1159 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k6_subset_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k6_subset_1 @ X27 @ X29 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k9_subset_1 @ X32 @ X30 @ X31 )
        = ( k3_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k6_subset_1 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
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
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LgjFVBmiqZ
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.64/6.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.64/6.83  % Solved by: fo/fo7.sh
% 6.64/6.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.64/6.83  % done 1568 iterations in 6.381s
% 6.64/6.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.64/6.83  % SZS output start Refutation
% 6.64/6.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.64/6.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.64/6.83  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.64/6.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.64/6.83  thf(sk_A_type, type, sk_A: $i).
% 6.64/6.83  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 6.64/6.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.64/6.83  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 6.64/6.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.64/6.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.64/6.83  thf(sk_B_type, type, sk_B: $i).
% 6.64/6.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.64/6.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.64/6.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.64/6.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.64/6.83  thf(t32_subset_1, conjecture,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83       ( ![C:$i]:
% 6.64/6.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83           ( ( k7_subset_1 @ A @ B @ C ) =
% 6.64/6.83             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 6.64/6.83  thf(zf_stmt_0, negated_conjecture,
% 6.64/6.83    (~( ![A:$i,B:$i]:
% 6.64/6.83        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83          ( ![C:$i]:
% 6.64/6.83            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83              ( ( k7_subset_1 @ A @ B @ C ) =
% 6.64/6.83                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 6.64/6.83    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 6.64/6.83  thf('0', plain,
% 6.64/6.83      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 6.64/6.83         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 6.64/6.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.83  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.83  thf(d2_subset_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( ( ( v1_xboole_0 @ A ) =>
% 6.64/6.83         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.64/6.83       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.64/6.83         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.64/6.83  thf('2', plain,
% 6.64/6.83      (![X17 : $i, X18 : $i]:
% 6.64/6.83         (~ (m1_subset_1 @ X17 @ X18)
% 6.64/6.83          | (r2_hidden @ X17 @ X18)
% 6.64/6.83          | (v1_xboole_0 @ X18))),
% 6.64/6.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.64/6.83  thf('3', plain,
% 6.64/6.83      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.64/6.83        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 6.64/6.83      inference('sup-', [status(thm)], ['1', '2'])).
% 6.64/6.83  thf(fc1_subset_1, axiom,
% 6.64/6.83    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.64/6.83  thf('4', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 6.64/6.83      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.64/6.83  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('clc', [status(thm)], ['3', '4'])).
% 6.64/6.83  thf(d1_zfmisc_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 6.64/6.83       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 6.64/6.83  thf('6', plain,
% 6.64/6.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.64/6.83         (~ (r2_hidden @ X15 @ X14)
% 6.64/6.83          | (r1_tarski @ X15 @ X13)
% 6.64/6.83          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 6.64/6.83      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.64/6.83  thf('7', plain,
% 6.64/6.83      (![X13 : $i, X15 : $i]:
% 6.64/6.83         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 6.64/6.83      inference('simplify', [status(thm)], ['6'])).
% 6.64/6.83  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 6.64/6.83      inference('sup-', [status(thm)], ['5', '7'])).
% 6.64/6.83  thf(t28_xboole_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.64/6.83  thf('9', plain,
% 6.64/6.83      (![X7 : $i, X8 : $i]:
% 6.64/6.83         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 6.64/6.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.64/6.83  thf('10', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 6.64/6.83      inference('sup-', [status(thm)], ['8', '9'])).
% 6.64/6.83  thf(commutativity_k3_xboole_0, axiom,
% 6.64/6.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.64/6.83  thf('11', plain,
% 6.64/6.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.64/6.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.64/6.83  thf(t100_xboole_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.64/6.83  thf('12', plain,
% 6.64/6.83      (![X2 : $i, X3 : $i]:
% 6.64/6.83         ((k4_xboole_0 @ X2 @ X3)
% 6.64/6.83           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.64/6.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.64/6.83  thf(redefinition_k6_subset_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.64/6.83  thf('13', plain,
% 6.64/6.83      (![X25 : $i, X26 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.64/6.83  thf('14', plain,
% 6.64/6.83      (![X2 : $i, X3 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X2 @ X3)
% 6.64/6.83           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.64/6.83      inference('demod', [status(thm)], ['12', '13'])).
% 6.64/6.83  thf('15', plain,
% 6.64/6.83      (![X0 : $i, X1 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X0 @ X1)
% 6.64/6.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.64/6.83      inference('sup+', [status(thm)], ['11', '14'])).
% 6.64/6.83  thf('16', plain,
% 6.64/6.83      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 6.64/6.83      inference('sup+', [status(thm)], ['10', '15'])).
% 6.64/6.83  thf('17', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.83  thf(d5_subset_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 6.64/6.83  thf('18', plain,
% 6.64/6.83      (![X20 : $i, X21 : $i]:
% 6.64/6.83         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 6.64/6.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 6.64/6.83      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.64/6.83  thf('19', plain,
% 6.64/6.83      (![X25 : $i, X26 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.64/6.83  thf('20', plain,
% 6.64/6.83      (![X20 : $i, X21 : $i]:
% 6.64/6.83         (((k3_subset_1 @ X20 @ X21) = (k6_subset_1 @ X20 @ X21))
% 6.64/6.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 6.64/6.83      inference('demod', [status(thm)], ['18', '19'])).
% 6.64/6.83  thf('21', plain,
% 6.64/6.83      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 6.64/6.83      inference('sup-', [status(thm)], ['17', '20'])).
% 6.64/6.83  thf('22', plain,
% 6.64/6.83      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 6.64/6.83      inference('sup+', [status(thm)], ['16', '21'])).
% 6.64/6.83  thf('23', plain,
% 6.64/6.83      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 6.64/6.83         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 6.64/6.83      inference('demod', [status(thm)], ['0', '22'])).
% 6.64/6.83  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.83  thf(redefinition_k7_subset_1, axiom,
% 6.64/6.83    (![A:$i,B:$i,C:$i]:
% 6.64/6.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 6.64/6.83  thf('25', plain,
% 6.64/6.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.64/6.83         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 6.64/6.83          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.64/6.83  thf('26', plain,
% 6.64/6.83      (![X25 : $i, X26 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.64/6.83  thf('27', plain,
% 6.64/6.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.64/6.83         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 6.64/6.83          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k6_subset_1 @ X27 @ X29)))),
% 6.64/6.83      inference('demod', [status(thm)], ['25', '26'])).
% 6.64/6.83  thf('28', plain,
% 6.64/6.83      (![X0 : $i]:
% 6.64/6.83         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 6.64/6.83      inference('sup-', [status(thm)], ['24', '27'])).
% 6.64/6.83  thf('29', plain,
% 6.64/6.83      (((k6_subset_1 @ sk_B @ sk_C_1)
% 6.64/6.83         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 6.64/6.83      inference('demod', [status(thm)], ['23', '28'])).
% 6.64/6.83  thf('30', plain,
% 6.64/6.83      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 6.64/6.83      inference('sup+', [status(thm)], ['10', '15'])).
% 6.64/6.83  thf(dt_k6_subset_1, axiom,
% 6.64/6.83    (![A:$i,B:$i]:
% 6.64/6.83     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 6.64/6.83  thf('31', plain,
% 6.64/6.83      (![X22 : $i, X23 : $i]:
% 6.64/6.83         (m1_subset_1 @ (k6_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))),
% 6.64/6.83      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 6.64/6.83  thf('32', plain,
% 6.64/6.83      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('sup+', [status(thm)], ['30', '31'])).
% 6.64/6.83  thf(redefinition_k9_subset_1, axiom,
% 6.64/6.83    (![A:$i,B:$i,C:$i]:
% 6.64/6.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.83       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 6.64/6.83  thf('33', plain,
% 6.64/6.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.64/6.83         (((k9_subset_1 @ X32 @ X30 @ X31) = (k3_xboole_0 @ X30 @ X31))
% 6.64/6.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.64/6.83  thf('34', plain,
% 6.64/6.83      (![X0 : $i]:
% 6.64/6.83         ((k9_subset_1 @ sk_A @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 6.64/6.83           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 6.64/6.83      inference('sup-', [status(thm)], ['32', '33'])).
% 6.64/6.83  thf('35', plain,
% 6.64/6.83      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 6.64/6.83      inference('sup+', [status(thm)], ['10', '15'])).
% 6.64/6.83  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.83  thf('37', plain,
% 6.64/6.83      (![X17 : $i, X18 : $i]:
% 6.64/6.83         (~ (m1_subset_1 @ X17 @ X18)
% 6.64/6.83          | (r2_hidden @ X17 @ X18)
% 6.64/6.83          | (v1_xboole_0 @ X18))),
% 6.64/6.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.64/6.83  thf('38', plain,
% 6.64/6.83      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.64/6.83        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 6.64/6.83      inference('sup-', [status(thm)], ['36', '37'])).
% 6.64/6.83  thf('39', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 6.64/6.83      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.64/6.83  thf('40', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.64/6.83      inference('clc', [status(thm)], ['38', '39'])).
% 6.64/6.83  thf('41', plain,
% 6.64/6.83      (![X13 : $i, X15 : $i]:
% 6.64/6.83         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 6.64/6.83      inference('simplify', [status(thm)], ['6'])).
% 6.64/6.83  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 6.64/6.83      inference('sup-', [status(thm)], ['40', '41'])).
% 6.64/6.83  thf('43', plain,
% 6.64/6.83      (![X7 : $i, X8 : $i]:
% 6.64/6.83         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 6.64/6.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.64/6.83  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 6.64/6.83      inference('sup-', [status(thm)], ['42', '43'])).
% 6.64/6.83  thf(t49_xboole_1, axiom,
% 6.64/6.83    (![A:$i,B:$i,C:$i]:
% 6.64/6.83     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.64/6.83       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 6.64/6.83  thf('45', plain,
% 6.64/6.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.64/6.83         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 6.64/6.83           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 6.64/6.83      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.64/6.83  thf('46', plain,
% 6.64/6.83      (![X25 : $i, X26 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.64/6.83  thf('47', plain,
% 6.64/6.83      (![X25 : $i, X26 : $i]:
% 6.64/6.83         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 6.64/6.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 6.64/6.83  thf('48', plain,
% 6.64/6.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.64/6.83         ((k3_xboole_0 @ X9 @ (k6_subset_1 @ X10 @ X11))
% 6.64/6.83           = (k6_subset_1 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 6.64/6.83      inference('demod', [status(thm)], ['45', '46', '47'])).
% 6.64/6.83  thf('49', plain,
% 6.64/6.83      (![X0 : $i]:
% 6.64/6.83         ((k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ X0))
% 6.64/6.83           = (k6_subset_1 @ sk_B @ X0))),
% 6.64/6.83      inference('sup+', [status(thm)], ['44', '48'])).
% 6.64/6.83  thf('50', plain,
% 6.64/6.83      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 6.64/6.83         = (k6_subset_1 @ sk_B @ sk_C_1))),
% 6.64/6.83      inference('sup+', [status(thm)], ['35', '49'])).
% 6.64/6.83  thf('51', plain,
% 6.64/6.83      (((k6_subset_1 @ sk_B @ sk_C_1) != (k6_subset_1 @ sk_B @ sk_C_1))),
% 6.64/6.83      inference('demod', [status(thm)], ['29', '34', '50'])).
% 6.64/6.83  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 6.64/6.83  
% 6.64/6.83  % SZS output end Refutation
% 6.64/6.83  
% 6.64/6.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
