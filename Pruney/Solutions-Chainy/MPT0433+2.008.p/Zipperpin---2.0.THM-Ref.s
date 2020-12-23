%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tLRL0kX7ip

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:38 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 197 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  421 (1442 expanded)
%              Number of equality atoms :   24 ( 128 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X26 @ X25 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    inference(clc,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['23','28'])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tLRL0kX7ip
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.40/1.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.40/1.60  % Solved by: fo/fo7.sh
% 1.40/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.40/1.60  % done 2163 iterations in 1.130s
% 1.40/1.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.40/1.60  % SZS output start Refutation
% 1.40/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.40/1.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.40/1.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.40/1.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.40/1.60  thf(sk_B_type, type, sk_B: $i).
% 1.40/1.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.40/1.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.40/1.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.40/1.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.40/1.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.40/1.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.40/1.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.40/1.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.40/1.60  thf(commutativity_k2_tarski, axiom,
% 1.40/1.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.40/1.60  thf('0', plain,
% 1.40/1.60      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 1.40/1.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.40/1.60  thf(t12_setfam_1, axiom,
% 1.40/1.60    (![A:$i,B:$i]:
% 1.40/1.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.40/1.60  thf('1', plain,
% 1.40/1.60      (![X18 : $i, X19 : $i]:
% 1.40/1.60         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 1.40/1.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.40/1.60  thf('2', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.40/1.60      inference('sup+', [status(thm)], ['0', '1'])).
% 1.40/1.60  thf('3', plain,
% 1.40/1.60      (![X18 : $i, X19 : $i]:
% 1.40/1.60         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 1.40/1.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.40/1.60  thf('4', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.40/1.60      inference('sup+', [status(thm)], ['2', '3'])).
% 1.40/1.60  thf(t51_xboole_1, axiom,
% 1.40/1.60    (![A:$i,B:$i]:
% 1.40/1.60     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.40/1.60       ( A ) ))).
% 1.40/1.60  thf('5', plain,
% 1.40/1.60      (![X5 : $i, X6 : $i]:
% 1.40/1.60         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 1.40/1.60           = (X5))),
% 1.40/1.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.40/1.60  thf('6', plain,
% 1.40/1.60      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 1.40/1.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.40/1.60  thf(l51_zfmisc_1, axiom,
% 1.40/1.60    (![A:$i,B:$i]:
% 1.40/1.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.40/1.60  thf('7', plain,
% 1.40/1.60      (![X16 : $i, X17 : $i]:
% 1.40/1.60         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 1.40/1.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.40/1.60  thf('8', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.40/1.60      inference('sup+', [status(thm)], ['6', '7'])).
% 1.40/1.60  thf('9', plain,
% 1.40/1.60      (![X16 : $i, X17 : $i]:
% 1.40/1.60         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 1.40/1.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.40/1.60  thf('10', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.40/1.60      inference('sup+', [status(thm)], ['8', '9'])).
% 1.40/1.60  thf('11', plain,
% 1.40/1.60      (![X5 : $i, X6 : $i]:
% 1.40/1.60         ((k2_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.40/1.60           = (X5))),
% 1.40/1.60      inference('demod', [status(thm)], ['5', '10'])).
% 1.40/1.60  thf('12', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.40/1.60      inference('sup+', [status(thm)], ['8', '9'])).
% 1.40/1.60  thf(t7_xboole_1, axiom,
% 1.40/1.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.40/1.60  thf('13', plain,
% 1.40/1.60      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.40/1.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.40/1.60  thf('14', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.40/1.60      inference('sup+', [status(thm)], ['12', '13'])).
% 1.40/1.60  thf('15', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.40/1.60      inference('sup+', [status(thm)], ['11', '14'])).
% 1.40/1.60  thf(t12_xboole_1, axiom,
% 1.40/1.60    (![A:$i,B:$i]:
% 1.40/1.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.40/1.60  thf('16', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 1.40/1.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.40/1.60  thf('17', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.40/1.60      inference('sup-', [status(thm)], ['15', '16'])).
% 1.40/1.60  thf('18', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.40/1.60      inference('sup+', [status(thm)], ['8', '9'])).
% 1.40/1.60  thf('19', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.40/1.60      inference('demod', [status(thm)], ['17', '18'])).
% 1.40/1.60  thf(t13_relat_1, axiom,
% 1.40/1.60    (![A:$i]:
% 1.40/1.60     ( ( v1_relat_1 @ A ) =>
% 1.40/1.60       ( ![B:$i]:
% 1.40/1.60         ( ( v1_relat_1 @ B ) =>
% 1.40/1.60           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 1.40/1.60             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.40/1.60  thf('20', plain,
% 1.40/1.60      (![X25 : $i, X26 : $i]:
% 1.40/1.60         (~ (v1_relat_1 @ X25)
% 1.40/1.60          | ((k1_relat_1 @ (k2_xboole_0 @ X26 @ X25))
% 1.40/1.60              = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25)))
% 1.40/1.60          | ~ (v1_relat_1 @ X26))),
% 1.40/1.60      inference('cnf', [status(esa)], [t13_relat_1])).
% 1.40/1.60  thf('21', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.40/1.60      inference('sup+', [status(thm)], ['12', '13'])).
% 1.40/1.60  thf('22', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.40/1.60           (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.40/1.60          | ~ (v1_relat_1 @ X1)
% 1.40/1.60          | ~ (v1_relat_1 @ X0))),
% 1.40/1.60      inference('sup+', [status(thm)], ['20', '21'])).
% 1.40/1.60  thf('23', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.40/1.60           (k1_relat_1 @ X0))
% 1.40/1.60          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.40/1.60          | ~ (v1_relat_1 @ X0))),
% 1.40/1.60      inference('sup+', [status(thm)], ['19', '22'])).
% 1.40/1.60  thf('24', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.40/1.60      inference('sup+', [status(thm)], ['11', '14'])).
% 1.40/1.60  thf(t3_subset, axiom,
% 1.40/1.60    (![A:$i,B:$i]:
% 1.40/1.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.40/1.60  thf('25', plain,
% 1.40/1.60      (![X20 : $i, X22 : $i]:
% 1.40/1.60         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.40/1.60      inference('cnf', [status(esa)], [t3_subset])).
% 1.40/1.60  thf('26', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.40/1.60      inference('sup-', [status(thm)], ['24', '25'])).
% 1.40/1.60  thf(cc2_relat_1, axiom,
% 1.40/1.60    (![A:$i]:
% 1.40/1.60     ( ( v1_relat_1 @ A ) =>
% 1.40/1.60       ( ![B:$i]:
% 1.40/1.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.40/1.60  thf('27', plain,
% 1.40/1.60      (![X23 : $i, X24 : $i]:
% 1.40/1.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.40/1.60          | (v1_relat_1 @ X23)
% 1.40/1.60          | ~ (v1_relat_1 @ X24))),
% 1.40/1.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.40/1.60  thf('28', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.40/1.60      inference('sup-', [status(thm)], ['26', '27'])).
% 1.40/1.60  thf('29', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         (~ (v1_relat_1 @ X0)
% 1.40/1.60          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.40/1.60             (k1_relat_1 @ X0)))),
% 1.40/1.60      inference('clc', [status(thm)], ['23', '28'])).
% 1.40/1.60  thf('30', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.40/1.60           (k1_relat_1 @ X0))
% 1.40/1.60          | ~ (v1_relat_1 @ X0))),
% 1.40/1.60      inference('sup+', [status(thm)], ['4', '29'])).
% 1.40/1.60  thf('31', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         (~ (v1_relat_1 @ X0)
% 1.40/1.60          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.40/1.60             (k1_relat_1 @ X0)))),
% 1.40/1.60      inference('clc', [status(thm)], ['23', '28'])).
% 1.40/1.60  thf(t19_xboole_1, axiom,
% 1.40/1.60    (![A:$i,B:$i,C:$i]:
% 1.40/1.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.40/1.60       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.40/1.60  thf('32', plain,
% 1.40/1.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.40/1.60         (~ (r1_tarski @ X2 @ X3)
% 1.40/1.60          | ~ (r1_tarski @ X2 @ X4)
% 1.40/1.60          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.40/1.60      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.40/1.60  thf('33', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.40/1.60         (~ (v1_relat_1 @ X0)
% 1.40/1.60          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.40/1.60             (k3_xboole_0 @ (k1_relat_1 @ X0) @ X2))
% 1.40/1.60          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 1.40/1.60      inference('sup-', [status(thm)], ['31', '32'])).
% 1.40/1.60  thf('34', plain,
% 1.40/1.60      (![X0 : $i, X1 : $i]:
% 1.40/1.60         (~ (v1_relat_1 @ X0)
% 1.40/1.60          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.40/1.60             (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 1.40/1.60          | ~ (v1_relat_1 @ X1))),
% 1.40/1.60      inference('sup-', [status(thm)], ['30', '33'])).
% 1.40/1.60  thf(t14_relat_1, conjecture,
% 1.40/1.60    (![A:$i]:
% 1.40/1.60     ( ( v1_relat_1 @ A ) =>
% 1.40/1.60       ( ![B:$i]:
% 1.40/1.60         ( ( v1_relat_1 @ B ) =>
% 1.40/1.60           ( r1_tarski @
% 1.40/1.60             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.40/1.60             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.40/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.40/1.60    (~( ![A:$i]:
% 1.40/1.60        ( ( v1_relat_1 @ A ) =>
% 1.40/1.60          ( ![B:$i]:
% 1.40/1.60            ( ( v1_relat_1 @ B ) =>
% 1.40/1.60              ( r1_tarski @
% 1.40/1.60                ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.40/1.60                ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 1.40/1.60    inference('cnf.neg', [status(esa)], [t14_relat_1])).
% 1.40/1.60  thf('35', plain,
% 1.40/1.60      (~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.40/1.60          (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.40/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.60  thf('36', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.40/1.60      inference('sup-', [status(thm)], ['34', '35'])).
% 1.40/1.60  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 1.40/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.60  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 1.40/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.60  thf('39', plain, ($false),
% 1.40/1.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.40/1.60  
% 1.40/1.60  % SZS output end Refutation
% 1.40/1.60  
% 1.40/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
