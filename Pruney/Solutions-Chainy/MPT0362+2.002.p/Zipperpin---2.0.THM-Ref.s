%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z2iUPsvFHp

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:56 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  427 ( 661 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t42_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k9_subset_1 @ X26 @ X24 @ X25 )
        = ( k3_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C_2 )
      = ( k3_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_C_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X29 @ X27 )
      | ( r1_tarski @ ( k3_subset_1 @ X28 @ X27 ) @ ( k3_subset_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['5','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z2iUPsvFHp
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 551 iterations in 0.221s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.67  thf(t42_subset_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67       ( ![C:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67           ( r1_tarski @
% 0.45/0.67             ( k3_subset_1 @ A @ B ) @ 
% 0.45/0.67             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67          ( ![C:$i]:
% 0.45/0.67            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67              ( r1_tarski @
% 0.45/0.67                ( k3_subset_1 @ A @ B ) @ 
% 0.45/0.67                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.45/0.67          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k9_subset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.67         (((k9_subset_1 @ X26 @ X24 @ X25) = (k3_xboole_0 @ X24 @ X25))
% 0.45/0.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k9_subset_1 @ sk_A @ X0 @ sk_C_2) = (k3_xboole_0 @ X0 @ sk_C_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.45/0.67          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_C_2 @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.45/0.67  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d2_subset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.67         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.67       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.67         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X20 @ X21)
% 0.45/0.67          | (r2_hidden @ X20 @ X21)
% 0.45/0.67          | (v1_xboole_0 @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.67        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(fc1_subset_1, axiom,
% 0.45/0.67    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.67  thf('9', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.67  thf('10', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf(d1_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X18 @ X17)
% 0.45/0.67          | (r1_tarski @ X18 @ X16)
% 0.45/0.67          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X16 : $i, X18 : $i]:
% 0.45/0.67         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.67  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['10', '12'])).
% 0.45/0.67  thf(d3_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X3 : $i, X5 : $i]:
% 0.45/0.67         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf(d4_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.67       ( ![D:$i]:
% 0.45/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.67           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X10 @ X9)
% 0.45/0.67          | (r2_hidden @ X10 @ X8)
% 0.45/0.67          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.45/0.67         ((r2_hidden @ X10 @ X8)
% 0.45/0.67          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X3 : $i, X5 : $i]:
% 0.45/0.67         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.67          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf(t1_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.67       ( r1_tarski @ A @ C ) ))).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.67         (~ (r1_tarski @ X12 @ X13)
% 0.45/0.67          | ~ (r1_tarski @ X13 @ X14)
% 0.45/0.67          | (r1_tarski @ X12 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.67         (~ (r1_tarski @ X15 @ X16)
% 0.45/0.67          | (r2_hidden @ X15 @ X17)
% 0.45/0.67          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i]:
% 0.45/0.67         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 0.45/0.67      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (r2_hidden @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['23', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X20 @ X21)
% 0.45/0.67          | (m1_subset_1 @ X20 @ X21)
% 0.45/0.67          | (v1_xboole_0 @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.67          | (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('29', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['28', '29'])).
% 0.45/0.67  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t31_subset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67       ( ![C:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67           ( ( r1_tarski @ B @ C ) <=>
% 0.45/0.67             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.45/0.67          | ~ (r1_tarski @ X29 @ X27)
% 0.45/0.67          | (r1_tarski @ (k3_subset_1 @ X28 @ X27) @ (k3_subset_1 @ X28 @ X29))
% 0.45/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.67          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.45/0.67             (k3_subset_1 @ sk_A @ X0))
% 0.45/0.67          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.45/0.67          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.45/0.67             (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['30', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.45/0.67          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain, ($false), inference('demod', [status(thm)], ['5', '36'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
