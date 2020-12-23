%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tRJF4Zvdjj

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  441 ( 695 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X9 @ X11 ) ) ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','14'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','25'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

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

thf('32',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tRJF4Zvdjj
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:38:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 438 iterations in 0.200s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.64  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.64  thf('0', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.64  thf(t31_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( r1_tarski @
% 0.46/0.64       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.46/0.64       ( k2_xboole_0 @ B @ C ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.64         (r1_tarski @ 
% 0.46/0.64          (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)) @ 
% 0.46/0.64          (k2_xboole_0 @ X10 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.46/0.64  thf(t12_setfam_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.64         (r1_tarski @ 
% 0.46/0.64          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X9 @ X10)) @ 
% 0.46/0.64           (k1_setfam_1 @ (k2_tarski @ X9 @ X11))) @ 
% 0.46/0.64          (k2_xboole_0 @ X10 @ X11))),
% 0.46/0.64      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.46/0.64          (k2_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '4'])).
% 0.46/0.64  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.46/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf(t25_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v1_relat_1 @ B ) =>
% 0.46/0.64           ( ( r1_tarski @ A @ B ) =>
% 0.46/0.64             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.46/0.64               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X26)
% 0.46/0.64          | (r1_tarski @ (k2_relat_1 @ X27) @ (k2_relat_1 @ X26))
% 0.46/0.64          | ~ (r1_tarski @ X27 @ X26)
% 0.46/0.64          | ~ (v1_relat_1 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.46/0.64             (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.46/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf(t3_subset, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X21 : $i, X23 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.46/0.64          (k1_zfmisc_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf(cc2_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.46/0.64          | (v1_relat_1 @ X24)
% 0.46/0.64          | ~ (v1_relat_1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.46/0.64             (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['9', '14'])).
% 0.46/0.64  thf(t17_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X26)
% 0.46/0.64          | (r1_tarski @ (k2_relat_1 @ X27) @ (k2_relat_1 @ X26))
% 0.46/0.64          | ~ (r1_tarski @ X27 @ X26)
% 0.46/0.64          | ~ (v1_relat_1 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.46/0.64             (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2)) @ X1)),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X21 : $i, X23 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.46/0.64          (k1_zfmisc_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.46/0.64          | (v1_relat_1 @ X24)
% 0.46/0.64          | ~ (v1_relat_1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.46/0.64             (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['20', '25'])).
% 0.46/0.64  thf(t19_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.46/0.64       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X3 @ X5)
% 0.46/0.64          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X3 @ X5)
% 0.46/0.64          | (r1_tarski @ X3 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.46/0.64             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.46/0.64          | ~ (r1_tarski @ 
% 0.46/0.64               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.46/0.64             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '30'])).
% 0.46/0.64  thf(t27_relat_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v1_relat_1 @ B ) =>
% 0.46/0.64           ( r1_tarski @
% 0.46/0.64             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.46/0.64             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( v1_relat_1 @ A ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( v1_relat_1 @ B ) =>
% 0.46/0.64              ( r1_tarski @
% 0.46/0.64                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.46/0.64                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.46/0.64          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (~ (r1_tarski @ 
% 0.46/0.64          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.46/0.64          (k1_setfam_1 @ 
% 0.46/0.64           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.46/0.64  thf('36', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '35'])).
% 0.46/0.64  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('39', plain, ($false),
% 0.46/0.64      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
