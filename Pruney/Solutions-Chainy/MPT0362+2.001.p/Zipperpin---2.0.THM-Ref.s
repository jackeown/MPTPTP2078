%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZzYRNffjyH

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:55 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  440 ( 601 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','28'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k4_xboole_0 @ X9 @ X8 ) @ ( k4_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZzYRNffjyH
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.74/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.95  % Solved by: fo/fo7.sh
% 0.74/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.95  % done 1390 iterations in 0.500s
% 0.74/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.95  % SZS output start Refutation
% 0.74/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.95  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.74/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.95  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.74/0.95  thf(t42_subset_1, conjecture,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.95       ( ![C:$i]:
% 0.74/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.95           ( r1_tarski @
% 0.74/0.95             ( k3_subset_1 @ A @ B ) @ 
% 0.74/0.95             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.74/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.95    (~( ![A:$i,B:$i]:
% 0.74/0.95        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.95          ( ![C:$i]:
% 0.74/0.95            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.95              ( r1_tarski @
% 0.74/0.95                ( k3_subset_1 @ A @ B ) @ 
% 0.74/0.95                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.74/0.95    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.74/0.95  thf('0', plain,
% 0.74/0.95      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.74/0.95          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(redefinition_k9_subset_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.95       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.74/0.95  thf('2', plain,
% 0.74/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.74/0.95         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.74/0.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.74/0.95  thf('3', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.74/0.95      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.95  thf('4', plain,
% 0.74/0.95      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.74/0.95          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.74/0.95      inference('demod', [status(thm)], ['0', '3'])).
% 0.74/0.95  thf(t48_xboole_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.95  thf('5', plain,
% 0.74/0.95      (![X12 : $i, X13 : $i]:
% 0.74/0.95         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.74/0.95           = (k3_xboole_0 @ X12 @ X13))),
% 0.74/0.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.95  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(d2_subset_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( ( v1_xboole_0 @ A ) =>
% 0.74/0.95         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.74/0.95       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.74/0.95         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.95  thf('7', plain,
% 0.74/0.95      (![X19 : $i, X20 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X19 @ X20)
% 0.74/0.95          | (r2_hidden @ X19 @ X20)
% 0.74/0.95          | (v1_xboole_0 @ X20))),
% 0.74/0.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.74/0.95  thf('8', plain,
% 0.74/0.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.74/0.95        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['6', '7'])).
% 0.74/0.95  thf(fc1_subset_1, axiom,
% 0.74/0.95    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.74/0.95  thf('9', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.74/0.95      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.74/0.95  thf('10', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('clc', [status(thm)], ['8', '9'])).
% 0.74/0.95  thf(d1_zfmisc_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.74/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.74/0.95  thf('11', plain,
% 0.74/0.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.74/0.95         (~ (r2_hidden @ X17 @ X16)
% 0.74/0.95          | (r1_tarski @ X17 @ X15)
% 0.74/0.95          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.74/0.95      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.74/0.95  thf('12', plain,
% 0.74/0.95      (![X15 : $i, X17 : $i]:
% 0.74/0.95         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 0.74/0.95      inference('simplify', [status(thm)], ['11'])).
% 0.74/0.95  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.74/0.95      inference('sup-', [status(thm)], ['10', '12'])).
% 0.74/0.95  thf(t12_xboole_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.74/0.95  thf('14', plain,
% 0.74/0.95      (![X5 : $i, X6 : $i]:
% 0.74/0.95         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.74/0.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.74/0.95  thf('15', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.74/0.95  thf(commutativity_k2_xboole_0, axiom,
% 0.74/0.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.74/0.95  thf('16', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.74/0.95  thf(t36_xboole_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.95  thf('17', plain,
% 0.74/0.95      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.74/0.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.95  thf(t10_xboole_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.74/0.95  thf('18', plain,
% 0.74/0.95      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.95         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.74/0.95  thf('19', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['17', '18'])).
% 0.74/0.95  thf('20', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 0.74/0.95      inference('sup+', [status(thm)], ['16', '19'])).
% 0.74/0.95  thf('21', plain,
% 0.74/0.95      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.74/0.95      inference('sup+', [status(thm)], ['15', '20'])).
% 0.74/0.95  thf('22', plain,
% 0.74/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.95         (~ (r1_tarski @ X14 @ X15)
% 0.74/0.95          | (r2_hidden @ X14 @ X16)
% 0.74/0.95          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.74/0.95      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.74/0.95  thf('23', plain,
% 0.74/0.95      (![X14 : $i, X15 : $i]:
% 0.74/0.95         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 0.74/0.95      inference('simplify', [status(thm)], ['22'])).
% 0.74/0.95  thf('24', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (r2_hidden @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['21', '23'])).
% 0.74/0.95  thf('25', plain,
% 0.74/0.95      (![X19 : $i, X20 : $i]:
% 0.74/0.95         (~ (r2_hidden @ X19 @ X20)
% 0.74/0.95          | (m1_subset_1 @ X19 @ X20)
% 0.74/0.95          | (v1_xboole_0 @ X20))),
% 0.74/0.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.74/0.95  thf('26', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.74/0.95          | (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.74/0.95  thf('27', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.74/0.95      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.74/0.95  thf('28', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.74/0.95  thf('29', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('sup+', [status(thm)], ['5', '28'])).
% 0.74/0.95  thf(d5_subset_1, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.95       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.74/0.95  thf('30', plain,
% 0.74/0.95      (![X22 : $i, X23 : $i]:
% 0.74/0.95         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.74/0.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.74/0.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.74/0.95  thf('31', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.74/0.95           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.95  thf('32', plain,
% 0.74/0.95      (![X12 : $i, X13 : $i]:
% 0.74/0.95         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.74/0.95           = (k3_xboole_0 @ X12 @ X13))),
% 0.74/0.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.95  thf('33', plain,
% 0.74/0.95      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.74/0.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.95  thf('34', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.74/0.95      inference('sup+', [status(thm)], ['32', '33'])).
% 0.74/0.95  thf(t34_xboole_1, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( r1_tarski @ A @ B ) =>
% 0.74/0.95       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.74/0.95  thf('35', plain,
% 0.74/0.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.74/0.95         (~ (r1_tarski @ X7 @ X8)
% 0.74/0.95          | (r1_tarski @ (k4_xboole_0 @ X9 @ X8) @ (k4_xboole_0 @ X9 @ X7)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.74/0.95  thf('36', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 0.74/0.95          (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['34', '35'])).
% 0.74/0.95  thf('37', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.74/0.95          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.74/0.95      inference('sup+', [status(thm)], ['31', '36'])).
% 0.74/0.95  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('39', plain,
% 0.74/0.95      (![X22 : $i, X23 : $i]:
% 0.74/0.95         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.74/0.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.74/0.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.74/0.95  thf('40', plain,
% 0.74/0.95      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.74/0.95  thf('41', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.74/0.95          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.74/0.95      inference('demod', [status(thm)], ['37', '40'])).
% 0.74/0.95  thf('42', plain, ($false), inference('demod', [status(thm)], ['4', '41'])).
% 0.74/0.95  
% 0.74/0.95  % SZS output end Refutation
% 0.74/0.95  
% 0.74/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
