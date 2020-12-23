%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8I67ah259Y

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:56 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   72 (  88 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  474 ( 656 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
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
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( m1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ( r1_tarski @ ( k3_subset_1 @ X24 @ X23 ) @ ( k3_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['5','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8I67ah259Y
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 1444 iterations in 0.518s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.97  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(t42_subset_1, conjecture,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ![C:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97           ( r1_tarski @
% 0.76/0.97             ( k3_subset_1 @ A @ B ) @ 
% 0.76/0.97             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i]:
% 0.76/0.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97          ( ![C:$i]:
% 0.76/0.97            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97              ( r1_tarski @
% 0.76/0.97                ( k3_subset_1 @ A @ B ) @ 
% 0.76/0.97                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.76/0.97          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k9_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.97         (((k9_subset_1 @ X22 @ X20 @ X21) = (k3_xboole_0 @ X20 @ X21))
% 0.76/0.97          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.76/0.97          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(d2_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( v1_xboole_0 @ A ) =>
% 0.76/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.76/0.97       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X16 : $i, X17 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X16 @ X17)
% 0.76/0.97          | (r2_hidden @ X16 @ X17)
% 0.76/0.97          | (v1_xboole_0 @ X17))),
% 0.76/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.76/0.97        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf(fc1_subset_1, axiom,
% 0.76/0.97    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.97  thf('10', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.76/0.97  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('clc', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf(d1_zfmisc_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.76/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X14 @ X13)
% 0.76/0.97          | (r1_tarski @ X14 @ X12)
% 0.76/0.97          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X12 : $i, X14 : $i]:
% 0.76/0.97         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['12'])).
% 0.76/0.97  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['11', '13'])).
% 0.76/0.97  thf(t28_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.76/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.97  thf('16', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf(t22_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X7 : $i, X8 : $i]:
% 0.76/0.97         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.76/0.97      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.97  thf('20', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['16', '19'])).
% 0.76/0.97  thf(t17_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.76/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.97  thf(t10_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i]:
% 0.76/0.97         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.76/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 0.76/0.97           = (k3_xboole_0 @ X0 @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.76/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X11 @ X12)
% 0.76/0.97          | (r2_hidden @ X11 @ X13)
% 0.76/0.97          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i]:
% 0.76/0.97         ((r2_hidden @ X11 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X11 @ X12))),
% 0.76/0.97      inference('simplify', [status(thm)], ['28'])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (r2_hidden @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['27', '29'])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      (![X16 : $i, X17 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X16 @ X17)
% 0.76/0.97          | (m1_subset_1 @ X16 @ X17)
% 0.76/0.97          | (v1_xboole_0 @ X17))),
% 0.76/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.76/0.97          | (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf('33', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['32', '33'])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['26', '34'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.76/0.97          (k1_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['25', '35'])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['20', '36'])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['6', '37'])).
% 0.76/0.97  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t31_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ![C:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97           ( ( r1_tarski @ B @ C ) <=>
% 0.76/0.97             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.76/0.97          | ~ (r1_tarski @ X25 @ X23)
% 0.76/0.97          | (r1_tarski @ (k3_subset_1 @ X24 @ X23) @ (k3_subset_1 @ X24 @ X25))
% 0.76/0.97          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.76/0.97          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.76/0.97             (k3_subset_1 @ sk_A @ X0))
% 0.76/0.97          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.76/0.97          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.76/0.97             (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['38', '41'])).
% 0.76/0.97  thf('43', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.76/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.76/0.97      inference('sup+', [status(thm)], ['43', '44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.76/0.97          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['42', '45'])).
% 0.76/0.97  thf('47', plain, ($false), inference('demod', [status(thm)], ['5', '46'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
