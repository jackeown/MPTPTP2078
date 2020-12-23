%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vv91nEsLYl

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:28 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   72 (  84 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  466 ( 546 expanded)
%              Number of equality atoms :   54 (  66 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k6_subset_1 @ X57 @ X58 )
      = ( k4_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X19 @ X20 ) @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) )
      = X19 ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('7',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ o_0_0_xboole_0 )
      = X21 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k6_subset_1 @ X57 @ X58 )
      = ( k4_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k6_subset_1 @ X57 @ X58 )
      = ( k4_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r1_tarski @ X61 @ ( k1_relat_1 @ X62 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X62 @ X61 ) )
        = X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t191_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) )
          = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_relat_1])).

thf('37',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vv91nEsLYl
% 0.16/0.36  % Computer   : n016.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 14:36:34 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 796 iterations in 0.419s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.89  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.70/0.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.70/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.70/0.89  thf(t51_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.70/0.89       ( A ) ))).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (![X19 : $i, X20 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.70/0.89           = (X19))),
% 0.70/0.89      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.70/0.89  thf(t12_setfam_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (![X59 : $i, X60 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 0.70/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.89  thf(redefinition_k6_subset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X57 : $i, X58 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.70/0.89  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X19 : $i, X20 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k6_subset_1 @ X19 @ X20) @ 
% 0.70/0.89           (k1_setfam_1 @ (k2_tarski @ X19 @ X20))) = (X19))),
% 0.70/0.89      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.70/0.89  thf(t6_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X22 @ (k2_xboole_0 @ X22 @ X23))
% 0.70/0.89           = (k2_xboole_0 @ X22 @ X23))),
% 0.70/0.89      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.70/0.89  thf(t95_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k3_xboole_0 @ A @ B ) =
% 0.70/0.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X28 @ X29)
% 0.70/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ 
% 0.70/0.89              (k2_xboole_0 @ X28 @ X29)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (![X59 : $i, X60 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 0.70/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29))
% 0.70/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ 
% 0.70/0.89              (k2_xboole_0 @ X28 @ X29)))),
% 0.70/0.89      inference('demod', [status(thm)], ['6', '7'])).
% 0.70/0.89  thf(t91_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.89       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.70/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.70/0.89           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29))
% 0.70/0.89           = (k5_xboole_0 @ X28 @ 
% 0.70/0.89              (k5_xboole_0 @ X29 @ (k2_xboole_0 @ X28 @ X29))))),
% 0.70/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.70/0.89           = (k5_xboole_0 @ X1 @ 
% 0.70/0.89              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['5', '10'])).
% 0.70/0.89  thf(t92_xboole_1, axiom,
% 0.70/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.89  thf('12', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.70/0.89  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.70/0.89  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.70/0.89           = (k5_xboole_0 @ X1 @ o_0_0_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['11', '14'])).
% 0.70/0.89  thf(t5_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('16', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.70/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.89  thf('17', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X21 : $i]: ((k5_xboole_0 @ X21 @ o_0_0_xboole_0) = (X21))),
% 0.70/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 0.70/0.89      inference('demod', [status(thm)], ['15', '18'])).
% 0.70/0.89  thf(t100_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X8 : $i, X9 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X8 @ X9)
% 0.70/0.89           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X57 : $i, X58 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (![X59 : $i, X60 : $i]:
% 0.70/0.89         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 0.70/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (![X8 : $i, X9 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X8 @ X9)
% 0.70/0.89           = (k5_xboole_0 @ X8 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9))))),
% 0.70/0.89      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.70/0.89           = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['19', '23'])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['24', '25'])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['4', '26'])).
% 0.70/0.89  thf(l32_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i]:
% 0.70/0.89         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.89  thf('29', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i]:
% 0.70/0.89         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (o_0_0_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X57 : $i, X58 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i]:
% 0.70/0.89         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (o_0_0_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['30', '31'])).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.70/0.89          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['27', '32'])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.70/0.89      inference('simplify', [status(thm)], ['33'])).
% 0.70/0.89  thf(t91_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ B ) =>
% 0.70/0.89       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.70/0.89         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X61 : $i, X62 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X61 @ (k1_relat_1 @ X62))
% 0.70/0.89          | ((k1_relat_1 @ (k7_relat_1 @ X62 @ X61)) = (X61))
% 0.70/0.89          | ~ (v1_relat_1 @ X62))),
% 0.70/0.89      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X0)
% 0.70/0.89          | ((k1_relat_1 @ 
% 0.70/0.89              (k7_relat_1 @ X0 @ (k6_subset_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.70/0.89              = (k6_subset_1 @ (k1_relat_1 @ X0) @ X1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.70/0.89  thf(t191_relat_1, conjecture,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ B ) =>
% 0.70/0.89       ( ( k1_relat_1 @
% 0.70/0.89           ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.70/0.89         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i]:
% 0.70/0.89        ( ( v1_relat_1 @ B ) =>
% 0.70/0.89          ( ( k1_relat_1 @
% 0.70/0.89              ( k7_relat_1 @ B @ ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) =
% 0.70/0.89            ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t191_relat_1])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (((k1_relat_1 @ 
% 0.70/0.89         (k7_relat_1 @ sk_B @ (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.70/0.89         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      ((((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.70/0.89          != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.70/0.89        | ~ (v1_relat_1 @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['36', '37'])).
% 0.70/0.89  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.70/0.89         != (k6_subset_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['38', '39'])).
% 0.70/0.89  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
