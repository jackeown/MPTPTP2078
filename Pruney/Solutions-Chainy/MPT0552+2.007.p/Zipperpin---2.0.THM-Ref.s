%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DwwFBcYuLX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:24 EST 2020

% Result     : Theorem 7.45s
% Output     : Refutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :   60 (  92 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  457 ( 774 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t108_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X18 @ X19 ) @ ( k7_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t108_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DwwFBcYuLX
% 0.16/0.37  % Computer   : n025.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 12:50:21 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 7.45/7.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.45/7.66  % Solved by: fo/fo7.sh
% 7.45/7.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.45/7.66  % done 7162 iterations in 7.179s
% 7.45/7.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.45/7.66  % SZS output start Refutation
% 7.45/7.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.45/7.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.45/7.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.45/7.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.45/7.66  thf(sk_B_type, type, sk_B: $i).
% 7.45/7.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.45/7.66  thf(sk_C_type, type, sk_C: $i).
% 7.45/7.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.45/7.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.45/7.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.45/7.66  thf(sk_A_type, type, sk_A: $i).
% 7.45/7.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.45/7.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 7.45/7.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 7.45/7.66  thf(commutativity_k2_tarski, axiom,
% 7.45/7.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 7.45/7.66  thf('0', plain,
% 7.45/7.66      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 7.45/7.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.45/7.66  thf(t12_setfam_1, axiom,
% 7.45/7.66    (![A:$i,B:$i]:
% 7.45/7.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.45/7.66  thf('1', plain,
% 7.45/7.66      (![X9 : $i, X10 : $i]:
% 7.45/7.66         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 7.45/7.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.45/7.66  thf('2', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]:
% 7.45/7.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 7.45/7.66      inference('sup+', [status(thm)], ['0', '1'])).
% 7.45/7.66  thf('3', plain,
% 7.45/7.66      (![X9 : $i, X10 : $i]:
% 7.45/7.66         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 7.45/7.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.45/7.66  thf('4', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.45/7.66      inference('sup+', [status(thm)], ['2', '3'])).
% 7.45/7.66  thf(t148_relat_1, axiom,
% 7.45/7.66    (![A:$i,B:$i]:
% 7.45/7.66     ( ( v1_relat_1 @ B ) =>
% 7.45/7.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 7.45/7.66  thf('5', plain,
% 7.45/7.66      (![X21 : $i, X22 : $i]:
% 7.45/7.66         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 7.45/7.66          | ~ (v1_relat_1 @ X21))),
% 7.45/7.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.45/7.66  thf('6', plain,
% 7.45/7.66      (![X21 : $i, X22 : $i]:
% 7.45/7.66         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 7.45/7.66          | ~ (v1_relat_1 @ X21))),
% 7.45/7.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.45/7.66  thf(t108_relat_1, axiom,
% 7.45/7.66    (![A:$i,B:$i,C:$i]:
% 7.45/7.66     ( ( v1_relat_1 @ C ) =>
% 7.45/7.66       ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 7.45/7.66         ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 7.45/7.66  thf('7', plain,
% 7.45/7.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.45/7.66         (((k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 7.45/7.66            = (k3_xboole_0 @ (k7_relat_1 @ X18 @ X19) @ 
% 7.45/7.66               (k7_relat_1 @ X18 @ X20)))
% 7.45/7.66          | ~ (v1_relat_1 @ X18))),
% 7.45/7.66      inference('cnf', [status(esa)], [t108_relat_1])).
% 7.45/7.66  thf(t17_xboole_1, axiom,
% 7.45/7.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 7.45/7.66  thf('8', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 7.45/7.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 7.45/7.66  thf(t25_relat_1, axiom,
% 7.45/7.66    (![A:$i]:
% 7.45/7.66     ( ( v1_relat_1 @ A ) =>
% 7.45/7.66       ( ![B:$i]:
% 7.45/7.66         ( ( v1_relat_1 @ B ) =>
% 7.45/7.66           ( ( r1_tarski @ A @ B ) =>
% 7.45/7.66             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 7.45/7.66               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 7.45/7.66  thf('9', plain,
% 7.45/7.66      (![X23 : $i, X24 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X23)
% 7.45/7.66          | (r1_tarski @ (k2_relat_1 @ X24) @ (k2_relat_1 @ X23))
% 7.45/7.66          | ~ (r1_tarski @ X24 @ X23)
% 7.45/7.66          | ~ (v1_relat_1 @ X24))),
% 7.45/7.66      inference('cnf', [status(esa)], [t25_relat_1])).
% 7.45/7.66  thf('10', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 7.45/7.66          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.45/7.66             (k2_relat_1 @ X0))
% 7.45/7.66          | ~ (v1_relat_1 @ X0))),
% 7.45/7.66      inference('sup-', [status(thm)], ['8', '9'])).
% 7.45/7.66  thf('11', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 7.45/7.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 7.45/7.66  thf(t3_subset, axiom,
% 7.45/7.66    (![A:$i,B:$i]:
% 7.45/7.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.45/7.66  thf('12', plain,
% 7.45/7.66      (![X11 : $i, X13 : $i]:
% 7.45/7.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 7.45/7.66      inference('cnf', [status(esa)], [t3_subset])).
% 7.45/7.66  thf('13', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]:
% 7.45/7.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 7.45/7.66      inference('sup-', [status(thm)], ['11', '12'])).
% 7.45/7.66  thf(cc2_relat_1, axiom,
% 7.45/7.66    (![A:$i]:
% 7.45/7.66     ( ( v1_relat_1 @ A ) =>
% 7.45/7.66       ( ![B:$i]:
% 7.45/7.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 7.45/7.66  thf('14', plain,
% 7.45/7.66      (![X14 : $i, X15 : $i]:
% 7.45/7.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 7.45/7.66          | (v1_relat_1 @ X14)
% 7.45/7.66          | ~ (v1_relat_1 @ X15))),
% 7.45/7.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.45/7.66  thf('15', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 7.45/7.66      inference('sup-', [status(thm)], ['13', '14'])).
% 7.45/7.66  thf('16', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X0)
% 7.45/7.66          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.45/7.66             (k2_relat_1 @ X0)))),
% 7.45/7.66      inference('clc', [status(thm)], ['10', '15'])).
% 7.45/7.66  thf('17', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         ((r1_tarski @ 
% 7.45/7.66           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 7.45/7.66           (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 7.45/7.66          | ~ (v1_relat_1 @ X2)
% 7.45/7.66          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 7.45/7.66      inference('sup+', [status(thm)], ['7', '16'])).
% 7.45/7.66  thf(dt_k7_relat_1, axiom,
% 7.45/7.66    (![A:$i,B:$i]:
% 7.45/7.66     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 7.45/7.66  thf('18', plain,
% 7.45/7.66      (![X16 : $i, X17 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 7.45/7.66      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.45/7.66  thf('19', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X2)
% 7.45/7.66          | (r1_tarski @ 
% 7.45/7.66             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 7.45/7.66             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1))))),
% 7.45/7.66      inference('clc', [status(thm)], ['17', '18'])).
% 7.45/7.66  thf('20', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.45/7.66           (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 7.45/7.66          | ~ (v1_relat_1 @ X2)
% 7.45/7.66          | ~ (v1_relat_1 @ X2))),
% 7.45/7.66      inference('sup+', [status(thm)], ['6', '19'])).
% 7.45/7.66  thf('21', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X2)
% 7.45/7.66          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.45/7.66             (k2_relat_1 @ (k7_relat_1 @ X2 @ X1))))),
% 7.45/7.66      inference('simplify', [status(thm)], ['20'])).
% 7.45/7.66  thf('22', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 7.45/7.66           (k9_relat_1 @ X1 @ X0))
% 7.45/7.66          | ~ (v1_relat_1 @ X1)
% 7.45/7.66          | ~ (v1_relat_1 @ X1))),
% 7.45/7.66      inference('sup+', [status(thm)], ['5', '21'])).
% 7.45/7.66  thf('23', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X1)
% 7.45/7.66          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 7.45/7.66             (k9_relat_1 @ X1 @ X0)))),
% 7.45/7.66      inference('simplify', [status(thm)], ['22'])).
% 7.45/7.66  thf('24', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.45/7.66           (k9_relat_1 @ X2 @ X0))
% 7.45/7.66          | ~ (v1_relat_1 @ X2))),
% 7.45/7.66      inference('sup+', [status(thm)], ['4', '23'])).
% 7.45/7.66  thf('25', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X1)
% 7.45/7.66          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 7.45/7.66             (k9_relat_1 @ X1 @ X0)))),
% 7.45/7.66      inference('simplify', [status(thm)], ['22'])).
% 7.45/7.66  thf(t19_xboole_1, axiom,
% 7.45/7.66    (![A:$i,B:$i,C:$i]:
% 7.45/7.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 7.45/7.66       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.45/7.66  thf('26', plain,
% 7.45/7.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 7.45/7.66         (~ (r1_tarski @ X2 @ X3)
% 7.45/7.66          | ~ (r1_tarski @ X2 @ X4)
% 7.45/7.66          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 7.45/7.66      inference('cnf', [status(esa)], [t19_xboole_1])).
% 7.45/7.66  thf('27', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X1)
% 7.45/7.66          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 7.45/7.66             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 7.45/7.66          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 7.45/7.66      inference('sup-', [status(thm)], ['25', '26'])).
% 7.45/7.66  thf('28', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         (~ (v1_relat_1 @ X1)
% 7.45/7.66          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 7.45/7.66             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 7.45/7.66          | ~ (v1_relat_1 @ X1))),
% 7.45/7.66      inference('sup-', [status(thm)], ['24', '27'])).
% 7.45/7.66  thf('29', plain,
% 7.45/7.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.45/7.66         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 7.45/7.66           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 7.45/7.66          | ~ (v1_relat_1 @ X1))),
% 7.45/7.66      inference('simplify', [status(thm)], ['28'])).
% 7.45/7.66  thf(t154_relat_1, conjecture,
% 7.45/7.66    (![A:$i,B:$i,C:$i]:
% 7.45/7.66     ( ( v1_relat_1 @ C ) =>
% 7.45/7.66       ( r1_tarski @
% 7.45/7.66         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.45/7.66         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 7.45/7.66  thf(zf_stmt_0, negated_conjecture,
% 7.45/7.66    (~( ![A:$i,B:$i,C:$i]:
% 7.45/7.66        ( ( v1_relat_1 @ C ) =>
% 7.45/7.66          ( r1_tarski @
% 7.45/7.66            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.45/7.66            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 7.45/7.66    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 7.45/7.66  thf('30', plain,
% 7.45/7.66      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 7.45/7.66          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 7.45/7.66           (k9_relat_1 @ sk_C @ sk_B)))),
% 7.45/7.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.45/7.66  thf('31', plain, (~ (v1_relat_1 @ sk_C)),
% 7.45/7.66      inference('sup-', [status(thm)], ['29', '30'])).
% 7.45/7.66  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 7.45/7.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.45/7.66  thf('33', plain, ($false), inference('demod', [status(thm)], ['31', '32'])).
% 7.45/7.66  
% 7.45/7.66  % SZS output end Refutation
% 7.45/7.66  
% 7.45/7.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
