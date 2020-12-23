%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2fEbSD8Pws

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:45 EST 2020

% Result     : Theorem 9.81s
% Output     : Refutation 9.81s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  308 ( 568 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','15'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2fEbSD8Pws
% 0.13/0.37  % Computer   : n018.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:04:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 9.81/10.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.81/10.03  % Solved by: fo/fo7.sh
% 9.81/10.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.81/10.03  % done 8162 iterations in 9.536s
% 9.81/10.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.81/10.03  % SZS output start Refutation
% 9.81/10.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.81/10.03  thf(sk_A_type, type, sk_A: $i).
% 9.81/10.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.81/10.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.81/10.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.81/10.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.81/10.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.81/10.03  thf(sk_B_type, type, sk_B: $i).
% 9.81/10.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.81/10.03  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 9.81/10.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.81/10.03  thf(commutativity_k2_tarski, axiom,
% 9.81/10.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 9.81/10.03  thf('0', plain,
% 9.81/10.03      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 9.81/10.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.81/10.03  thf(t12_setfam_1, axiom,
% 9.81/10.03    (![A:$i,B:$i]:
% 9.81/10.03     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.81/10.03  thf('1', plain,
% 9.81/10.03      (![X13 : $i, X14 : $i]:
% 9.81/10.03         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 9.81/10.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.81/10.03  thf('2', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 9.81/10.03      inference('sup+', [status(thm)], ['0', '1'])).
% 9.81/10.03  thf('3', plain,
% 9.81/10.03      (![X13 : $i, X14 : $i]:
% 9.81/10.03         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 9.81/10.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.81/10.03  thf('4', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.81/10.03      inference('sup+', [status(thm)], ['2', '3'])).
% 9.81/10.03  thf(d10_xboole_0, axiom,
% 9.81/10.03    (![A:$i,B:$i]:
% 9.81/10.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.81/10.03  thf('5', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.81/10.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.81/10.03  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.81/10.03      inference('simplify', [status(thm)], ['5'])).
% 9.81/10.03  thf(t18_xboole_1, axiom,
% 9.81/10.03    (![A:$i,B:$i,C:$i]:
% 9.81/10.03     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 9.81/10.03  thf('7', plain,
% 9.81/10.03      (![X3 : $i, X4 : $i, X5 : $i]:
% 9.81/10.03         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 9.81/10.03      inference('cnf', [status(esa)], [t18_xboole_1])).
% 9.81/10.03  thf('8', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 9.81/10.03      inference('sup-', [status(thm)], ['6', '7'])).
% 9.81/10.03  thf(t25_relat_1, axiom,
% 9.81/10.03    (![A:$i]:
% 9.81/10.03     ( ( v1_relat_1 @ A ) =>
% 9.81/10.03       ( ![B:$i]:
% 9.81/10.03         ( ( v1_relat_1 @ B ) =>
% 9.81/10.03           ( ( r1_tarski @ A @ B ) =>
% 9.81/10.03             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 9.81/10.03               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 9.81/10.03  thf('9', plain,
% 9.81/10.03      (![X20 : $i, X21 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ X20)
% 9.81/10.03          | (r1_tarski @ (k2_relat_1 @ X21) @ (k2_relat_1 @ X20))
% 9.81/10.03          | ~ (r1_tarski @ X21 @ X20)
% 9.81/10.03          | ~ (v1_relat_1 @ X21))),
% 9.81/10.03      inference('cnf', [status(esa)], [t25_relat_1])).
% 9.81/10.03  thf('10', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 9.81/10.03          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.81/10.03             (k2_relat_1 @ X0))
% 9.81/10.03          | ~ (v1_relat_1 @ X0))),
% 9.81/10.03      inference('sup-', [status(thm)], ['8', '9'])).
% 9.81/10.03  thf('11', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 9.81/10.03      inference('sup-', [status(thm)], ['6', '7'])).
% 9.81/10.03  thf(t3_subset, axiom,
% 9.81/10.03    (![A:$i,B:$i]:
% 9.81/10.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.81/10.03  thf('12', plain,
% 9.81/10.03      (![X15 : $i, X17 : $i]:
% 9.81/10.03         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 9.81/10.03      inference('cnf', [status(esa)], [t3_subset])).
% 9.81/10.03  thf('13', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.81/10.03      inference('sup-', [status(thm)], ['11', '12'])).
% 9.81/10.03  thf(cc2_relat_1, axiom,
% 9.81/10.03    (![A:$i]:
% 9.81/10.03     ( ( v1_relat_1 @ A ) =>
% 9.81/10.03       ( ![B:$i]:
% 9.81/10.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.81/10.03  thf('14', plain,
% 9.81/10.03      (![X18 : $i, X19 : $i]:
% 9.81/10.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 9.81/10.03          | (v1_relat_1 @ X18)
% 9.81/10.03          | ~ (v1_relat_1 @ X19))),
% 9.81/10.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.81/10.03  thf('15', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.81/10.03      inference('sup-', [status(thm)], ['13', '14'])).
% 9.81/10.03  thf('16', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ X0)
% 9.81/10.03          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.81/10.03             (k2_relat_1 @ X0)))),
% 9.81/10.03      inference('clc', [status(thm)], ['10', '15'])).
% 9.81/10.03  thf('17', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.81/10.03           (k2_relat_1 @ X0))
% 9.81/10.03          | ~ (v1_relat_1 @ X0))),
% 9.81/10.03      inference('sup+', [status(thm)], ['4', '16'])).
% 9.81/10.03  thf('18', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ X0)
% 9.81/10.03          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.81/10.03             (k2_relat_1 @ X0)))),
% 9.81/10.03      inference('clc', [status(thm)], ['10', '15'])).
% 9.81/10.03  thf(t19_xboole_1, axiom,
% 9.81/10.03    (![A:$i,B:$i,C:$i]:
% 9.81/10.03     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 9.81/10.03       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 9.81/10.03  thf('19', plain,
% 9.81/10.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.81/10.03         (~ (r1_tarski @ X6 @ X7)
% 9.81/10.03          | ~ (r1_tarski @ X6 @ X8)
% 9.81/10.03          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 9.81/10.03      inference('cnf', [status(esa)], [t19_xboole_1])).
% 9.81/10.03  thf('20', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ X0)
% 9.81/10.03          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 9.81/10.03             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 9.81/10.03          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 9.81/10.03      inference('sup-', [status(thm)], ['18', '19'])).
% 9.81/10.03  thf('21', plain,
% 9.81/10.03      (![X0 : $i, X1 : $i]:
% 9.81/10.03         (~ (v1_relat_1 @ X0)
% 9.81/10.03          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.81/10.03             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 9.81/10.03          | ~ (v1_relat_1 @ X1))),
% 9.81/10.03      inference('sup-', [status(thm)], ['17', '20'])).
% 9.81/10.03  thf(t27_relat_1, conjecture,
% 9.81/10.03    (![A:$i]:
% 9.81/10.03     ( ( v1_relat_1 @ A ) =>
% 9.81/10.03       ( ![B:$i]:
% 9.81/10.03         ( ( v1_relat_1 @ B ) =>
% 9.81/10.03           ( r1_tarski @
% 9.81/10.03             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 9.81/10.03             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 9.81/10.03  thf(zf_stmt_0, negated_conjecture,
% 9.81/10.03    (~( ![A:$i]:
% 9.81/10.03        ( ( v1_relat_1 @ A ) =>
% 9.81/10.03          ( ![B:$i]:
% 9.81/10.03            ( ( v1_relat_1 @ B ) =>
% 9.81/10.03              ( r1_tarski @
% 9.81/10.03                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 9.81/10.03                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 9.81/10.03    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 9.81/10.03  thf('22', plain,
% 9.81/10.03      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 9.81/10.03          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 9.81/10.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.81/10.03  thf('23', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 9.81/10.03      inference('sup-', [status(thm)], ['21', '22'])).
% 9.81/10.03  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 9.81/10.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.81/10.03  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 9.81/10.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.81/10.03  thf('26', plain, ($false),
% 9.81/10.03      inference('demod', [status(thm)], ['23', '24', '25'])).
% 9.81/10.03  
% 9.81/10.03  % SZS output end Refutation
% 9.81/10.03  
% 9.81/10.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
