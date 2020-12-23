%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWbfity3va

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 137 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  472 (1134 expanded)
%              Number of equality atoms :   35 (  78 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
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

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('28',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('38',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','30','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWbfity3va
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 295 iterations in 0.402s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.68/0.86  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.86  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.68/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(t32_subset_1, conjecture,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86       ( ![C:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.68/0.86             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i]:
% 0.68/0.86        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86          ( ![C:$i]:
% 0.68/0.86            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.68/0.86                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.68/0.86  thf('0', plain,
% 0.68/0.86      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 0.68/0.86         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d2_subset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( v1_xboole_0 @ A ) =>
% 0.68/0.86         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.68/0.86       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.68/0.86         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X14 @ X15)
% 0.68/0.86          | (r2_hidden @ X14 @ X15)
% 0.68/0.86          | (v1_xboole_0 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.68/0.86        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf(fc1_subset_1, axiom,
% 0.68/0.86    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.86  thf('4', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.68/0.86  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('clc', [status(thm)], ['3', '4'])).
% 0.68/0.86  thf(d1_zfmisc_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.68/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.86         (~ (r2_hidden @ X12 @ X11)
% 0.68/0.86          | (r1_tarski @ X12 @ X10)
% 0.68/0.86          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.68/0.86      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X10 : $i, X12 : $i]:
% 0.68/0.86         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.68/0.86      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.86  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.68/0.86      inference('sup-', [status(thm)], ['5', '7'])).
% 0.68/0.86  thf(t28_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.86  thf('9', plain,
% 0.68/0.86      (![X4 : $i, X5 : $i]:
% 0.68/0.86         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.68/0.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.86  thf('10', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.86  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.86  thf(t100_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.86  thf('12', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ X2 @ X3)
% 0.68/0.86           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['11', '12'])).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['10', '13'])).
% 0.68/0.86  thf('15', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d5_subset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (![X17 : $i, X18 : $i]:
% 0.68/0.86         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.68/0.86          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.68/0.86      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.68/0.86  thf('17', plain,
% 0.68/0.86      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.86  thf('18', plain,
% 0.68/0.86      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['14', '17'])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 0.68/0.86         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 0.68/0.86      inference('demod', [status(thm)], ['0', '18'])).
% 0.68/0.86  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(redefinition_k7_subset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.68/0.86          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.86  thf('23', plain,
% 0.68/0.86      (((k4_xboole_0 @ sk_B @ sk_C_1)
% 0.68/0.86         != (k9_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 0.68/0.86      inference('demod', [status(thm)], ['19', '22'])).
% 0.68/0.86  thf('24', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(dt_k3_subset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.86  thf('25', plain,
% 0.68/0.86      (![X19 : $i, X20 : $i]:
% 0.68/0.86         ((m1_subset_1 @ (k3_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.68/0.86          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.68/0.86      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['14', '17'])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['26', '27'])).
% 0.68/0.86  thf(redefinition_k9_subset_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.86       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.68/0.86  thf('29', plain,
% 0.68/0.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.68/0.86         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.68/0.86          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.68/0.86      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k9_subset_1 @ sk_A @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.68/0.86           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['28', '29'])).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['10', '13'])).
% 0.68/0.86  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X14 @ X15)
% 0.68/0.86          | (r2_hidden @ X14 @ X15)
% 0.68/0.86          | (v1_xboole_0 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.68/0.86        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.86  thf('35', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.68/0.86  thf('36', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.68/0.86      inference('clc', [status(thm)], ['34', '35'])).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      (![X10 : $i, X12 : $i]:
% 0.68/0.86         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.68/0.86      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.86  thf('38', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.68/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.86  thf('39', plain,
% 0.68/0.86      (![X4 : $i, X5 : $i]:
% 0.68/0.86         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.68/0.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.86  thf('40', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.68/0.86      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.86  thf(t49_xboole_1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.68/0.86       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.68/0.86  thf('41', plain,
% 0.68/0.86      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.86         ((k3_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.68/0.86           = (k4_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8))),
% 0.68/0.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.86  thf('42', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.68/0.86           = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['40', '41'])).
% 0.68/0.86  thf('43', plain,
% 0.68/0.86      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.68/0.86         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['31', '42'])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      (((k4_xboole_0 @ sk_B @ sk_C_1) != (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.68/0.86      inference('demod', [status(thm)], ['23', '30', '43'])).
% 0.68/0.86  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
