%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lczogQhfgw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:56 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   68 (  84 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  453 ( 635 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( m1_subset_1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( r1_tarski @ ( k3_subset_1 @ X22 @ X21 ) @ ( k3_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['5','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lczogQhfgw
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.07  % Solved by: fo/fo7.sh
% 0.83/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.07  % done 1352 iterations in 0.606s
% 0.83/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.07  % SZS output start Refutation
% 0.83/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.07  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.83/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.07  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.83/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.83/1.07  thf(t42_subset_1, conjecture,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07       ( ![C:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07           ( r1_tarski @
% 0.83/1.07             ( k3_subset_1 @ A @ B ) @ 
% 0.83/1.07             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.07    (~( ![A:$i,B:$i]:
% 0.83/1.07        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07          ( ![C:$i]:
% 0.83/1.07            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07              ( r1_tarski @
% 0.83/1.07                ( k3_subset_1 @ A @ B ) @ 
% 0.83/1.07                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.83/1.07    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.83/1.07  thf('0', plain,
% 0.83/1.07      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.83/1.07          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(redefinition_k9_subset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.83/1.07  thf('2', plain,
% 0.83/1.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.83/1.07         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 0.83/1.07          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.83/1.07  thf('3', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.83/1.07  thf(commutativity_k3_xboole_0, axiom,
% 0.83/1.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.83/1.07  thf('4', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.83/1.07  thf('5', plain,
% 0.83/1.07      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.83/1.07          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.83/1.07      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.83/1.07  thf('6', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.83/1.07  thf(t17_xboole_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.83/1.07  thf('7', plain,
% 0.83/1.07      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.83/1.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.83/1.07  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(d2_subset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( v1_xboole_0 @ A ) =>
% 0.83/1.07         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.83/1.07       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.83/1.07         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.83/1.07  thf('9', plain,
% 0.83/1.07      (![X14 : $i, X15 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X14 @ X15)
% 0.83/1.07          | (r2_hidden @ X14 @ X15)
% 0.83/1.07          | (v1_xboole_0 @ X15))),
% 0.83/1.07      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.83/1.07  thf('10', plain,
% 0.83/1.07      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.83/1.07        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.07  thf(fc1_subset_1, axiom,
% 0.83/1.07    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.83/1.07  thf('11', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.83/1.07  thf('12', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['10', '11'])).
% 0.83/1.07  thf(d1_zfmisc_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.83/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.83/1.07  thf('13', plain,
% 0.83/1.07      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.07         (~ (r2_hidden @ X12 @ X11)
% 0.83/1.07          | (r1_tarski @ X12 @ X10)
% 0.83/1.07          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.83/1.07      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.83/1.07  thf('14', plain,
% 0.83/1.07      (![X10 : $i, X12 : $i]:
% 0.83/1.07         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['13'])).
% 0.83/1.07  thf('15', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.83/1.07      inference('sup-', [status(thm)], ['12', '14'])).
% 0.83/1.07  thf(t28_xboole_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.83/1.07  thf('16', plain,
% 0.83/1.07      (![X7 : $i, X8 : $i]:
% 0.83/1.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.83/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.83/1.07  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.83/1.07      inference('sup-', [status(thm)], ['15', '16'])).
% 0.83/1.07  thf('18', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.83/1.07  thf(t18_xboole_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.83/1.07  thf('19', plain,
% 0.83/1.07      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.83/1.07         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.83/1.07  thf('20', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.07         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['18', '19'])).
% 0.83/1.07  thf('21', plain,
% 0.83/1.07      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_tarski @ X0 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['17', '20'])).
% 0.83/1.07  thf('22', plain,
% 0.83/1.07      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.83/1.07      inference('sup-', [status(thm)], ['7', '21'])).
% 0.83/1.07  thf('23', plain,
% 0.83/1.07      (![X7 : $i, X8 : $i]:
% 0.83/1.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.83/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.83/1.07  thf('24', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.83/1.07           = (k3_xboole_0 @ sk_B @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.83/1.07  thf('25', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.83/1.07  thf('26', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.83/1.07           = (k3_xboole_0 @ sk_B @ X0))),
% 0.83/1.07      inference('demod', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf('27', plain,
% 0.83/1.07      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.83/1.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.83/1.07  thf('28', plain,
% 0.83/1.07      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.07         (~ (r1_tarski @ X9 @ X10)
% 0.83/1.07          | (r2_hidden @ X9 @ X11)
% 0.83/1.07          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.83/1.07      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.83/1.07  thf('29', plain,
% 0.83/1.07      (![X9 : $i, X10 : $i]:
% 0.83/1.07         ((r2_hidden @ X9 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X9 @ X10))),
% 0.83/1.07      inference('simplify', [status(thm)], ['28'])).
% 0.83/1.07  thf('30', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (r2_hidden @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['27', '29'])).
% 0.83/1.07  thf('31', plain,
% 0.83/1.07      (![X14 : $i, X15 : $i]:
% 0.83/1.07         (~ (r2_hidden @ X14 @ X15)
% 0.83/1.07          | (m1_subset_1 @ X14 @ X15)
% 0.83/1.07          | (v1_xboole_0 @ X15))),
% 0.83/1.07      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.83/1.07  thf('32', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.83/1.07          | (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['30', '31'])).
% 0.83/1.07  thf('33', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.83/1.07  thf('34', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.83/1.07      inference('clc', [status(thm)], ['32', '33'])).
% 0.83/1.07  thf('35', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.83/1.07      inference('sup+', [status(thm)], ['26', '34'])).
% 0.83/1.07  thf('36', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.83/1.07      inference('sup+', [status(thm)], ['6', '35'])).
% 0.83/1.07  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(t31_subset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07       ( ![C:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.07           ( ( r1_tarski @ B @ C ) <=>
% 0.83/1.07             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.83/1.07  thf('38', plain,
% 0.83/1.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.83/1.07          | ~ (r1_tarski @ X23 @ X21)
% 0.83/1.07          | (r1_tarski @ (k3_subset_1 @ X22 @ X21) @ (k3_subset_1 @ X22 @ X23))
% 0.83/1.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.83/1.07  thf('39', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.83/1.07          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.83/1.07             (k3_subset_1 @ sk_A @ X0))
% 0.83/1.07          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.83/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.83/1.07  thf('40', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.83/1.07          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.83/1.07             (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['36', '39'])).
% 0.83/1.07  thf('41', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.83/1.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.83/1.07  thf('42', plain,
% 0.83/1.07      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.83/1.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.83/1.07  thf('43', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.83/1.07      inference('sup+', [status(thm)], ['41', '42'])).
% 0.83/1.07  thf('44', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.83/1.07          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.83/1.07      inference('demod', [status(thm)], ['40', '43'])).
% 0.83/1.07  thf('45', plain, ($false), inference('demod', [status(thm)], ['5', '44'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.91/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
