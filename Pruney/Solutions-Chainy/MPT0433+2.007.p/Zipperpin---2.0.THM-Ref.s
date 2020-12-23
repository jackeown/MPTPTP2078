%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AKSbItKuBd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:38 EST 2020

% Result     : Theorem 56.42s
% Output     : Refutation 56.42s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 125 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  426 ( 902 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X28 @ X27 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','28'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t14_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_relat_1])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AKSbItKuBd
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 56.42/56.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 56.42/56.69  % Solved by: fo/fo7.sh
% 56.42/56.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.42/56.69  % done 24345 iterations in 56.235s
% 56.42/56.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 56.42/56.69  % SZS output start Refutation
% 56.42/56.69  thf(sk_A_type, type, sk_A: $i).
% 56.42/56.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 56.42/56.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 56.42/56.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 56.42/56.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 56.42/56.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 56.42/56.69  thf(sk_B_type, type, sk_B: $i).
% 56.42/56.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 56.42/56.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 56.42/56.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 56.42/56.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 56.42/56.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 56.42/56.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 56.42/56.69  thf(commutativity_k2_tarski, axiom,
% 56.42/56.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 56.42/56.69  thf('0', plain,
% 56.42/56.69      (![X11 : $i, X12 : $i]:
% 56.42/56.69         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 56.42/56.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 56.42/56.69  thf(t12_setfam_1, axiom,
% 56.42/56.69    (![A:$i,B:$i]:
% 56.42/56.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 56.42/56.69  thf('1', plain,
% 56.42/56.69      (![X20 : $i, X21 : $i]:
% 56.42/56.69         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 56.42/56.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 56.42/56.69  thf('2', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 56.42/56.69      inference('sup+', [status(thm)], ['0', '1'])).
% 56.42/56.69  thf('3', plain,
% 56.42/56.69      (![X20 : $i, X21 : $i]:
% 56.42/56.69         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 56.42/56.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 56.42/56.69  thf('4', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 56.42/56.69      inference('sup+', [status(thm)], ['2', '3'])).
% 56.42/56.69  thf(t48_xboole_1, axiom,
% 56.42/56.69    (![A:$i,B:$i]:
% 56.42/56.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 56.42/56.69  thf('5', plain,
% 56.42/56.69      (![X7 : $i, X8 : $i]:
% 56.42/56.69         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 56.42/56.69           = (k3_xboole_0 @ X7 @ X8))),
% 56.42/56.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.42/56.69  thf(t36_xboole_1, axiom,
% 56.42/56.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 56.42/56.69  thf('6', plain,
% 56.42/56.69      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 56.42/56.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.42/56.69  thf(t12_xboole_1, axiom,
% 56.42/56.69    (![A:$i,B:$i]:
% 56.42/56.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 56.42/56.69  thf('7', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 56.42/56.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 56.42/56.69  thf('8', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 56.42/56.69      inference('sup-', [status(thm)], ['6', '7'])).
% 56.42/56.69  thf('9', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 56.42/56.69      inference('sup+', [status(thm)], ['5', '8'])).
% 56.42/56.69  thf('10', plain,
% 56.42/56.69      (![X11 : $i, X12 : $i]:
% 56.42/56.69         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 56.42/56.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 56.42/56.69  thf(l51_zfmisc_1, axiom,
% 56.42/56.69    (![A:$i,B:$i]:
% 56.42/56.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 56.42/56.69  thf('11', plain,
% 56.42/56.69      (![X18 : $i, X19 : $i]:
% 56.42/56.69         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 56.42/56.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 56.42/56.69  thf('12', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 56.42/56.69      inference('sup+', [status(thm)], ['10', '11'])).
% 56.42/56.69  thf('13', plain,
% 56.42/56.69      (![X18 : $i, X19 : $i]:
% 56.42/56.69         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 56.42/56.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 56.42/56.69  thf('14', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.42/56.69      inference('sup+', [status(thm)], ['12', '13'])).
% 56.42/56.69  thf('15', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 56.42/56.69      inference('demod', [status(thm)], ['9', '14'])).
% 56.42/56.69  thf(t13_relat_1, axiom,
% 56.42/56.69    (![A:$i]:
% 56.42/56.69     ( ( v1_relat_1 @ A ) =>
% 56.42/56.69       ( ![B:$i]:
% 56.42/56.69         ( ( v1_relat_1 @ B ) =>
% 56.42/56.69           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 56.42/56.69             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 56.42/56.69  thf('16', plain,
% 56.42/56.69      (![X27 : $i, X28 : $i]:
% 56.42/56.69         (~ (v1_relat_1 @ X27)
% 56.42/56.69          | ((k1_relat_1 @ (k2_xboole_0 @ X28 @ X27))
% 56.42/56.69              = (k2_xboole_0 @ (k1_relat_1 @ X28) @ (k1_relat_1 @ X27)))
% 56.42/56.69          | ~ (v1_relat_1 @ X28))),
% 56.42/56.69      inference('cnf', [status(esa)], [t13_relat_1])).
% 56.42/56.69  thf('17', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 56.42/56.69      inference('sup+', [status(thm)], ['12', '13'])).
% 56.42/56.69  thf(t7_xboole_1, axiom,
% 56.42/56.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 56.42/56.69  thf('18', plain,
% 56.42/56.69      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 56.42/56.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 56.42/56.69  thf('19', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 56.42/56.69      inference('sup+', [status(thm)], ['17', '18'])).
% 56.42/56.69  thf('20', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 56.42/56.69           (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 56.42/56.69          | ~ (v1_relat_1 @ X1)
% 56.42/56.69          | ~ (v1_relat_1 @ X0))),
% 56.42/56.69      inference('sup+', [status(thm)], ['16', '19'])).
% 56.42/56.69  thf('21', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 56.42/56.69           (k1_relat_1 @ X0))
% 56.42/56.69          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 56.42/56.69          | ~ (v1_relat_1 @ X0))),
% 56.42/56.69      inference('sup+', [status(thm)], ['15', '20'])).
% 56.42/56.69  thf('22', plain,
% 56.42/56.69      (![X7 : $i, X8 : $i]:
% 56.42/56.69         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 56.42/56.69           = (k3_xboole_0 @ X7 @ X8))),
% 56.42/56.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.42/56.69  thf('23', plain,
% 56.42/56.69      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 56.42/56.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.42/56.69  thf('24', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 56.42/56.69      inference('sup+', [status(thm)], ['22', '23'])).
% 56.42/56.69  thf(t3_subset, axiom,
% 56.42/56.69    (![A:$i,B:$i]:
% 56.42/56.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 56.42/56.69  thf('25', plain,
% 56.42/56.69      (![X22 : $i, X24 : $i]:
% 56.42/56.69         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 56.42/56.69      inference('cnf', [status(esa)], [t3_subset])).
% 56.42/56.69  thf('26', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 56.42/56.69      inference('sup-', [status(thm)], ['24', '25'])).
% 56.42/56.69  thf(cc2_relat_1, axiom,
% 56.42/56.69    (![A:$i]:
% 56.42/56.69     ( ( v1_relat_1 @ A ) =>
% 56.42/56.69       ( ![B:$i]:
% 56.42/56.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 56.42/56.69  thf('27', plain,
% 56.42/56.69      (![X25 : $i, X26 : $i]:
% 56.42/56.69         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 56.42/56.69          | (v1_relat_1 @ X25)
% 56.42/56.69          | ~ (v1_relat_1 @ X26))),
% 56.42/56.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 56.42/56.69  thf('28', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 56.42/56.69      inference('sup-', [status(thm)], ['26', '27'])).
% 56.42/56.69  thf('29', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         (~ (v1_relat_1 @ X0)
% 56.42/56.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 56.42/56.69             (k1_relat_1 @ X0)))),
% 56.42/56.69      inference('clc', [status(thm)], ['21', '28'])).
% 56.42/56.69  thf('30', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.42/56.69           (k1_relat_1 @ X0))
% 56.42/56.69          | ~ (v1_relat_1 @ X0))),
% 56.42/56.69      inference('sup+', [status(thm)], ['4', '29'])).
% 56.42/56.69  thf('31', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         (~ (v1_relat_1 @ X0)
% 56.42/56.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 56.42/56.69             (k1_relat_1 @ X0)))),
% 56.42/56.69      inference('clc', [status(thm)], ['21', '28'])).
% 56.42/56.69  thf(t19_xboole_1, axiom,
% 56.42/56.69    (![A:$i,B:$i,C:$i]:
% 56.42/56.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 56.42/56.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 56.42/56.69  thf('32', plain,
% 56.42/56.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 56.42/56.69         (~ (r1_tarski @ X2 @ X3)
% 56.42/56.69          | ~ (r1_tarski @ X2 @ X4)
% 56.42/56.69          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 56.42/56.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 56.42/56.69  thf('33', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.42/56.69         (~ (v1_relat_1 @ X0)
% 56.42/56.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 56.42/56.69             (k3_xboole_0 @ (k1_relat_1 @ X0) @ X2))
% 56.42/56.69          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 56.42/56.69      inference('sup-', [status(thm)], ['31', '32'])).
% 56.42/56.69  thf('34', plain,
% 56.42/56.69      (![X0 : $i, X1 : $i]:
% 56.42/56.69         (~ (v1_relat_1 @ X0)
% 56.42/56.69          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.42/56.69             (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 56.42/56.69          | ~ (v1_relat_1 @ X1))),
% 56.42/56.69      inference('sup-', [status(thm)], ['30', '33'])).
% 56.42/56.69  thf(t14_relat_1, conjecture,
% 56.42/56.69    (![A:$i]:
% 56.42/56.69     ( ( v1_relat_1 @ A ) =>
% 56.42/56.69       ( ![B:$i]:
% 56.42/56.69         ( ( v1_relat_1 @ B ) =>
% 56.42/56.69           ( r1_tarski @
% 56.42/56.69             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 56.42/56.69             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 56.42/56.69  thf(zf_stmt_0, negated_conjecture,
% 56.42/56.69    (~( ![A:$i]:
% 56.42/56.69        ( ( v1_relat_1 @ A ) =>
% 56.42/56.69          ( ![B:$i]:
% 56.42/56.69            ( ( v1_relat_1 @ B ) =>
% 56.42/56.69              ( r1_tarski @
% 56.42/56.69                ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 56.42/56.69                ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 56.42/56.69    inference('cnf.neg', [status(esa)], [t14_relat_1])).
% 56.42/56.69  thf('35', plain,
% 56.42/56.69      (~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 56.42/56.69          (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 56.42/56.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.42/56.69  thf('36', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 56.42/56.69      inference('sup-', [status(thm)], ['34', '35'])).
% 56.42/56.69  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 56.42/56.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.42/56.69  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 56.42/56.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.42/56.69  thf('39', plain, ($false),
% 56.42/56.69      inference('demod', [status(thm)], ['36', '37', '38'])).
% 56.42/56.69  
% 56.42/56.69  % SZS output end Refutation
% 56.42/56.69  
% 56.42/56.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
