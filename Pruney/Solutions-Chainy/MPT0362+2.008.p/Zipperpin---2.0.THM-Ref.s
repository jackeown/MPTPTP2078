%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VGZjXHFao6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:56 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   70 (  85 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  481 ( 666 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t35_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ D ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X9 ) @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t35_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['4','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VGZjXHFao6
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:34:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.94/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.94/2.11  % Solved by: fo/fo7.sh
% 1.94/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.11  % done 1868 iterations in 1.662s
% 1.94/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.94/2.11  % SZS output start Refutation
% 1.94/2.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.94/2.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.94/2.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.11  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.94/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.94/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.94/2.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.94/2.11  thf(t42_subset_1, conjecture,
% 1.94/2.11    (![A:$i,B:$i]:
% 1.94/2.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.11       ( ![C:$i]:
% 1.94/2.11         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.11           ( r1_tarski @
% 1.94/2.11             ( k3_subset_1 @ A @ B ) @ 
% 1.94/2.11             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.94/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.11    (~( ![A:$i,B:$i]:
% 1.94/2.11        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.11          ( ![C:$i]:
% 1.94/2.11            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.11              ( r1_tarski @
% 1.94/2.11                ( k3_subset_1 @ A @ B ) @ 
% 1.94/2.11                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 1.94/2.11    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 1.94/2.11  thf('0', plain,
% 1.94/2.11      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.94/2.11          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.11  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.11  thf(redefinition_k9_subset_1, axiom,
% 1.94/2.11    (![A:$i,B:$i,C:$i]:
% 1.94/2.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.11       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.94/2.11  thf('2', plain,
% 1.94/2.11      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.94/2.11         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 1.94/2.11          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.94/2.11      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.94/2.11  thf('3', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 1.94/2.11      inference('sup-', [status(thm)], ['1', '2'])).
% 1.94/2.11  thf('4', plain,
% 1.94/2.11      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.94/2.11          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.94/2.11      inference('demod', [status(thm)], ['0', '3'])).
% 1.94/2.11  thf(d10_xboole_0, axiom,
% 1.94/2.11    (![A:$i,B:$i]:
% 1.94/2.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.94/2.11  thf('5', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.94/2.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.94/2.11  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.94/2.11      inference('simplify', [status(thm)], ['5'])).
% 1.94/2.11  thf(t48_xboole_1, axiom,
% 1.94/2.11    (![A:$i,B:$i]:
% 1.94/2.11     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.94/2.11  thf('7', plain,
% 1.94/2.11      (![X12 : $i, X13 : $i]:
% 1.94/2.11         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.94/2.11           = (k3_xboole_0 @ X12 @ X13))),
% 1.94/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.94/2.11  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.11  thf(d2_subset_1, axiom,
% 1.94/2.11    (![A:$i,B:$i]:
% 1.94/2.11     ( ( ( v1_xboole_0 @ A ) =>
% 1.94/2.11         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.94/2.11       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.94/2.11         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.94/2.11  thf('9', plain,
% 1.94/2.11      (![X19 : $i, X20 : $i]:
% 1.94/2.11         (~ (m1_subset_1 @ X19 @ X20)
% 1.94/2.11          | (r2_hidden @ X19 @ X20)
% 1.94/2.11          | (v1_xboole_0 @ X20))),
% 1.94/2.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.94/2.11  thf('10', plain,
% 1.94/2.11      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.94/2.11        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.94/2.11      inference('sup-', [status(thm)], ['8', '9'])).
% 1.94/2.11  thf(fc1_subset_1, axiom,
% 1.94/2.11    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.94/2.11  thf('11', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 1.94/2.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.94/2.11  thf('12', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('clc', [status(thm)], ['10', '11'])).
% 1.94/2.11  thf(d1_zfmisc_1, axiom,
% 1.94/2.11    (![A:$i,B:$i]:
% 1.94/2.11     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.94/2.11       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.94/2.11  thf('13', plain,
% 1.94/2.11      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.94/2.11         (~ (r2_hidden @ X17 @ X16)
% 1.94/2.11          | (r1_tarski @ X17 @ X15)
% 1.94/2.11          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 1.94/2.11      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.94/2.11  thf('14', plain,
% 1.94/2.11      (![X15 : $i, X17 : $i]:
% 1.94/2.11         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 1.94/2.11      inference('simplify', [status(thm)], ['13'])).
% 1.94/2.11  thf('15', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.94/2.11      inference('sup-', [status(thm)], ['12', '14'])).
% 1.94/2.11  thf(t36_xboole_1, axiom,
% 1.94/2.11    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.94/2.11  thf('16', plain,
% 1.94/2.11      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 1.94/2.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.94/2.11  thf(t1_xboole_1, axiom,
% 1.94/2.11    (![A:$i,B:$i,C:$i]:
% 1.94/2.11     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.94/2.11       ( r1_tarski @ A @ C ) ))).
% 1.94/2.11  thf('17', plain,
% 1.94/2.11      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.94/2.11         (~ (r1_tarski @ X3 @ X4)
% 1.94/2.11          | ~ (r1_tarski @ X4 @ X5)
% 1.94/2.11          | (r1_tarski @ X3 @ X5))),
% 1.94/2.11      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.94/2.11  thf('18', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.11         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.94/2.11      inference('sup-', [status(thm)], ['16', '17'])).
% 1.94/2.11  thf('19', plain,
% 1.94/2.11      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 1.94/2.11      inference('sup-', [status(thm)], ['15', '18'])).
% 1.94/2.11  thf('20', plain,
% 1.94/2.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.94/2.11         (~ (r1_tarski @ X14 @ X15)
% 1.94/2.11          | (r2_hidden @ X14 @ X16)
% 1.94/2.11          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 1.94/2.11      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.94/2.11  thf('21', plain,
% 1.94/2.11      (![X14 : $i, X15 : $i]:
% 1.94/2.11         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 1.94/2.11      inference('simplify', [status(thm)], ['20'])).
% 1.94/2.11  thf('22', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         (r2_hidden @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('sup-', [status(thm)], ['19', '21'])).
% 1.94/2.11  thf('23', plain,
% 1.94/2.11      (![X19 : $i, X20 : $i]:
% 1.94/2.11         (~ (r2_hidden @ X19 @ X20)
% 1.94/2.11          | (m1_subset_1 @ X19 @ X20)
% 1.94/2.11          | (v1_xboole_0 @ X20))),
% 1.94/2.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.94/2.11  thf('24', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.94/2.11          | (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 1.94/2.11      inference('sup-', [status(thm)], ['22', '23'])).
% 1.94/2.11  thf('25', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 1.94/2.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.94/2.11  thf('26', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('clc', [status(thm)], ['24', '25'])).
% 1.94/2.11  thf('27', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('sup+', [status(thm)], ['7', '26'])).
% 1.94/2.11  thf(d5_subset_1, axiom,
% 1.94/2.11    (![A:$i,B:$i]:
% 1.94/2.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.94/2.11       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.94/2.11  thf('28', plain,
% 1.94/2.11      (![X22 : $i, X23 : $i]:
% 1.94/2.11         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 1.94/2.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 1.94/2.11      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.94/2.11  thf('29', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.94/2.11           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.94/2.11      inference('sup-', [status(thm)], ['27', '28'])).
% 1.94/2.11  thf('30', plain,
% 1.94/2.11      (![X12 : $i, X13 : $i]:
% 1.94/2.11         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.94/2.11           = (k3_xboole_0 @ X12 @ X13))),
% 1.94/2.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.94/2.11  thf('31', plain,
% 1.94/2.11      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 1.94/2.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.94/2.11  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.94/2.11      inference('simplify', [status(thm)], ['5'])).
% 1.94/2.11  thf(t35_xboole_1, axiom,
% 1.94/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.11     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 1.94/2.11       ( r1_tarski @ ( k4_xboole_0 @ A @ D ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.94/2.11  thf('33', plain,
% 1.94/2.11      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.94/2.11         (~ (r1_tarski @ X6 @ X7)
% 1.94/2.11          | ~ (r1_tarski @ X8 @ X9)
% 1.94/2.11          | (r1_tarski @ (k4_xboole_0 @ X6 @ X9) @ (k4_xboole_0 @ X7 @ X8)))),
% 1.94/2.11      inference('cnf', [status(esa)], [t35_xboole_1])).
% 1.94/2.11  thf('34', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.11         ((r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X0 @ X1))
% 1.94/2.11          | ~ (r1_tarski @ X1 @ X2))),
% 1.94/2.11      inference('sup-', [status(thm)], ['32', '33'])).
% 1.94/2.11  thf('35', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.11         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 1.94/2.11          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.94/2.11      inference('sup-', [status(thm)], ['31', '34'])).
% 1.94/2.11  thf('36', plain,
% 1.94/2.11      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.94/2.11         (~ (r1_tarski @ X3 @ X4)
% 1.94/2.11          | ~ (r1_tarski @ X4 @ X5)
% 1.94/2.11          | (r1_tarski @ X3 @ X5))),
% 1.94/2.11      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.94/2.11  thf('37', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.94/2.11         ((r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X3)
% 1.94/2.11          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3))),
% 1.94/2.11      inference('sup-', [status(thm)], ['35', '36'])).
% 1.94/2.11  thf('38', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.94/2.11         (~ (r1_tarski @ (k4_xboole_0 @ X3 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 1.94/2.11          | (r1_tarski @ (k4_xboole_0 @ X3 @ X1) @ X2))),
% 1.94/2.11      inference('sup-', [status(thm)], ['30', '37'])).
% 1.94/2.11  thf('39', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ X1)
% 1.94/2.11          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X1))),
% 1.94/2.11      inference('sup-', [status(thm)], ['29', '38'])).
% 1.94/2.11  thf('40', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.11  thf('41', plain,
% 1.94/2.11      (![X22 : $i, X23 : $i]:
% 1.94/2.11         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 1.94/2.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 1.94/2.11      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.94/2.11  thf('42', plain,
% 1.94/2.11      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.94/2.11      inference('sup-', [status(thm)], ['40', '41'])).
% 1.94/2.11  thf('43', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ X1)
% 1.94/2.11          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X1))),
% 1.94/2.11      inference('demod', [status(thm)], ['39', '42'])).
% 1.94/2.11  thf('44', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.94/2.11          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.94/2.11      inference('sup-', [status(thm)], ['6', '43'])).
% 1.94/2.11  thf('45', plain, ($false), inference('demod', [status(thm)], ['4', '44'])).
% 1.94/2.11  
% 1.94/2.11  % SZS output end Refutation
% 1.94/2.11  
% 1.94/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
