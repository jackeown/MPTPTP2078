%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r0N23PFbuB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:55 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 183 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  581 (1410 expanded)
%              Number of equality atoms :   21 (  67 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k1_relat_1 @ X59 ) @ ( k1_relat_1 @ X58 ) )
      | ~ ( r1_tarski @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X57: $i] :
      ( ( ( k3_relat_1 @ X57 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k2_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('26',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X17 ) ) ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('31',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ X8 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k2_relat_1 @ X59 ) @ ( k2_relat_1 @ X58 ) )
      | ~ ( r1_tarski @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r0N23PFbuB
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.76/2.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.76/2.99  % Solved by: fo/fo7.sh
% 2.76/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.76/2.99  % done 5495 iterations in 2.533s
% 2.76/2.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.76/2.99  % SZS output start Refutation
% 2.76/2.99  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.76/2.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.76/2.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.76/2.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.76/2.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.76/2.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.76/2.99  thf(sk_B_type, type, sk_B: $i).
% 2.76/2.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.76/2.99  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.76/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.76/2.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.76/2.99  thf(t31_relat_1, conjecture,
% 2.76/2.99    (![A:$i]:
% 2.76/2.99     ( ( v1_relat_1 @ A ) =>
% 2.76/2.99       ( ![B:$i]:
% 2.76/2.99         ( ( v1_relat_1 @ B ) =>
% 2.76/2.99           ( ( r1_tarski @ A @ B ) =>
% 2.76/2.99             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.76/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.76/2.99    (~( ![A:$i]:
% 2.76/2.99        ( ( v1_relat_1 @ A ) =>
% 2.76/2.99          ( ![B:$i]:
% 2.76/2.99            ( ( v1_relat_1 @ B ) =>
% 2.76/2.99              ( ( r1_tarski @ A @ B ) =>
% 2.76/2.99                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 2.76/2.99    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 2.76/2.99  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(d6_relat_1, axiom,
% 2.76/2.99    (![A:$i]:
% 2.76/2.99     ( ( v1_relat_1 @ A ) =>
% 2.76/2.99       ( ( k3_relat_1 @ A ) =
% 2.76/2.99         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.76/2.99  thf('1', plain,
% 2.76/2.99      (![X57 : $i]:
% 2.76/2.99         (((k3_relat_1 @ X57)
% 2.76/2.99            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 2.76/2.99          | ~ (v1_relat_1 @ X57))),
% 2.76/2.99      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.76/2.99  thf('2', plain,
% 2.76/2.99      (![X57 : $i]:
% 2.76/2.99         (((k3_relat_1 @ X57)
% 2.76/2.99            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 2.76/2.99          | ~ (v1_relat_1 @ X57))),
% 2.76/2.99      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.76/2.99  thf(d10_xboole_0, axiom,
% 2.76/2.99    (![A:$i,B:$i]:
% 2.76/2.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.76/2.99  thf('3', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.76/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.76/2.99  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.76/2.99      inference('simplify', [status(thm)], ['3'])).
% 2.76/2.99  thf(t11_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.76/2.99  thf('5', plain,
% 2.76/2.99      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.76/2.99         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 2.76/2.99      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.76/2.99  thf('6', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['4', '5'])).
% 2.76/2.99  thf('7', plain,
% 2.76/2.99      (![X0 : $i]:
% 2.76/2.99         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.76/2.99          | ~ (v1_relat_1 @ X0))),
% 2.76/2.99      inference('sup+', [status(thm)], ['2', '6'])).
% 2.76/2.99  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf(t25_relat_1, axiom,
% 2.76/2.99    (![A:$i]:
% 2.76/2.99     ( ( v1_relat_1 @ A ) =>
% 2.76/2.99       ( ![B:$i]:
% 2.76/2.99         ( ( v1_relat_1 @ B ) =>
% 2.76/2.99           ( ( r1_tarski @ A @ B ) =>
% 2.76/2.99             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 2.76/2.99               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 2.76/2.99  thf('9', plain,
% 2.76/2.99      (![X58 : $i, X59 : $i]:
% 2.76/2.99         (~ (v1_relat_1 @ X58)
% 2.76/2.99          | (r1_tarski @ (k1_relat_1 @ X59) @ (k1_relat_1 @ X58))
% 2.76/2.99          | ~ (r1_tarski @ X59 @ X58)
% 2.76/2.99          | ~ (v1_relat_1 @ X59))),
% 2.76/2.99      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.76/2.99  thf('10', plain,
% 2.76/2.99      ((~ (v1_relat_1 @ sk_A)
% 2.76/2.99        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 2.76/2.99        | ~ (v1_relat_1 @ sk_B))),
% 2.76/2.99      inference('sup-', [status(thm)], ['8', '9'])).
% 2.76/2.99  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['10', '11', '12'])).
% 2.76/2.99  thf(t1_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.76/2.99       ( r1_tarski @ A @ C ) ))).
% 2.76/2.99  thf('14', plain,
% 2.76/2.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.76/2.99         (~ (r1_tarski @ X10 @ X11)
% 2.76/2.99          | ~ (r1_tarski @ X11 @ X12)
% 2.76/2.99          | (r1_tarski @ X10 @ X12))),
% 2.76/2.99      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.76/2.99  thf('15', plain,
% 2.76/2.99      (![X0 : $i]:
% 2.76/2.99         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 2.76/2.99          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['13', '14'])).
% 2.76/2.99  thf('16', plain,
% 2.76/2.99      ((~ (v1_relat_1 @ sk_B)
% 2.76/2.99        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['7', '15'])).
% 2.76/2.99  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['16', '17'])).
% 2.76/2.99  thf('19', plain,
% 2.76/2.99      (![X57 : $i]:
% 2.76/2.99         (((k3_relat_1 @ X57)
% 2.76/2.99            = (k2_xboole_0 @ (k1_relat_1 @ X57) @ (k2_relat_1 @ X57)))
% 2.76/2.99          | ~ (v1_relat_1 @ X57))),
% 2.76/2.99      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.76/2.99  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.76/2.99      inference('simplify', [status(thm)], ['3'])).
% 2.76/2.99  thf(t28_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i]:
% 2.76/2.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.76/2.99  thf('21', plain,
% 2.76/2.99      (![X13 : $i, X14 : $i]:
% 2.76/2.99         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.76/2.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.76/2.99  thf(t12_setfam_1, axiom,
% 2.76/2.99    (![A:$i,B:$i]:
% 2.76/2.99     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.76/2.99  thf('22', plain,
% 2.76/2.99      (![X50 : $i, X51 : $i]:
% 2.76/2.99         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 2.76/2.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.76/2.99  thf('23', plain,
% 2.76/2.99      (![X13 : $i, X14 : $i]:
% 2.76/2.99         (((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (X13))
% 2.76/2.99          | ~ (r1_tarski @ X13 @ X14))),
% 2.76/2.99      inference('demod', [status(thm)], ['21', '22'])).
% 2.76/2.99  thf('24', plain,
% 2.76/2.99      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['20', '23'])).
% 2.76/2.99  thf(t31_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( r1_tarski @
% 2.76/2.99       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 2.76/2.99       ( k2_xboole_0 @ B @ C ) ))).
% 2.76/2.99  thf('25', plain,
% 2.76/2.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.76/2.99         (r1_tarski @ 
% 2.76/2.99          (k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k3_xboole_0 @ X15 @ X17)) @ 
% 2.76/2.99          (k2_xboole_0 @ X16 @ X17))),
% 2.76/2.99      inference('cnf', [status(esa)], [t31_xboole_1])).
% 2.76/2.99  thf('26', plain,
% 2.76/2.99      (![X50 : $i, X51 : $i]:
% 2.76/2.99         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 2.76/2.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.76/2.99  thf('27', plain,
% 2.76/2.99      (![X50 : $i, X51 : $i]:
% 2.76/2.99         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 2.76/2.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.76/2.99  thf('28', plain,
% 2.76/2.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.76/2.99         (r1_tarski @ 
% 2.76/2.99          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16)) @ 
% 2.76/2.99           (k1_setfam_1 @ (k2_tarski @ X15 @ X17))) @ 
% 2.76/2.99          (k2_xboole_0 @ X16 @ X17))),
% 2.76/2.99      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.76/2.99  thf('29', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]:
% 2.76/2.99         (r1_tarski @ 
% 2.76/2.99          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0) @ 
% 2.76/2.99          (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('sup+', [status(thm)], ['24', '28'])).
% 2.76/2.99  thf(t17_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.76/2.99  thf('30', plain,
% 2.76/2.99      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 2.76/2.99      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.76/2.99  thf('31', plain,
% 2.76/2.99      (![X50 : $i, X51 : $i]:
% 2.76/2.99         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 2.76/2.99      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.76/2.99  thf('32', plain,
% 2.76/2.99      (![X8 : $i, X9 : $i]:
% 2.76/2.99         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ X8)),
% 2.76/2.99      inference('demod', [status(thm)], ['30', '31'])).
% 2.76/2.99  thf(t12_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i]:
% 2.76/2.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.76/2.99  thf('33', plain,
% 2.76/2.99      (![X6 : $i, X7 : $i]:
% 2.76/2.99         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 2.76/2.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.76/2.99  thf('34', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]:
% 2.76/2.99         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0) = (X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['32', '33'])).
% 2.76/2.99  thf('35', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('demod', [status(thm)], ['29', '34'])).
% 2.76/2.99  thf('36', plain,
% 2.76/2.99      (![X0 : $i]:
% 2.76/2.99         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 2.76/2.99          | ~ (v1_relat_1 @ X0))),
% 2.76/2.99      inference('sup+', [status(thm)], ['19', '35'])).
% 2.76/2.99  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('38', plain,
% 2.76/2.99      (![X58 : $i, X59 : $i]:
% 2.76/2.99         (~ (v1_relat_1 @ X58)
% 2.76/2.99          | (r1_tarski @ (k2_relat_1 @ X59) @ (k2_relat_1 @ X58))
% 2.76/2.99          | ~ (r1_tarski @ X59 @ X58)
% 2.76/2.99          | ~ (v1_relat_1 @ X59))),
% 2.76/2.99      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.76/2.99  thf('39', plain,
% 2.76/2.99      ((~ (v1_relat_1 @ sk_A)
% 2.76/2.99        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 2.76/2.99        | ~ (v1_relat_1 @ sk_B))),
% 2.76/2.99      inference('sup-', [status(thm)], ['37', '38'])).
% 2.76/2.99  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.76/2.99  thf('43', plain,
% 2.76/2.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.76/2.99         (~ (r1_tarski @ X10 @ X11)
% 2.76/2.99          | ~ (r1_tarski @ X11 @ X12)
% 2.76/2.99          | (r1_tarski @ X10 @ X12))),
% 2.76/2.99      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.76/2.99  thf('44', plain,
% 2.76/2.99      (![X0 : $i]:
% 2.76/2.99         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 2.76/2.99          | ~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['42', '43'])).
% 2.76/2.99  thf('45', plain,
% 2.76/2.99      ((~ (v1_relat_1 @ sk_B)
% 2.76/2.99        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['36', '44'])).
% 2.76/2.99  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['45', '46'])).
% 2.76/2.99  thf(t8_xboole_1, axiom,
% 2.76/2.99    (![A:$i,B:$i,C:$i]:
% 2.76/2.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.76/2.99       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.76/2.99  thf('48', plain,
% 2.76/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.76/2.99         (~ (r1_tarski @ X18 @ X19)
% 2.76/2.99          | ~ (r1_tarski @ X20 @ X19)
% 2.76/2.99          | (r1_tarski @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 2.76/2.99      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.76/2.99  thf('49', plain,
% 2.76/2.99      (![X0 : $i]:
% 2.76/2.99         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 2.76/2.99           (k3_relat_1 @ sk_B))
% 2.76/2.99          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['47', '48'])).
% 2.76/2.99  thf('50', plain,
% 2.76/2.99      ((r1_tarski @ 
% 2.76/2.99        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 2.76/2.99        (k3_relat_1 @ sk_B))),
% 2.76/2.99      inference('sup-', [status(thm)], ['18', '49'])).
% 2.76/2.99  thf('51', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['4', '5'])).
% 2.76/2.99  thf('52', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('demod', [status(thm)], ['29', '34'])).
% 2.76/2.99  thf('53', plain,
% 2.76/2.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.76/2.99         (~ (r1_tarski @ X18 @ X19)
% 2.76/2.99          | ~ (r1_tarski @ X20 @ X19)
% 2.76/2.99          | (r1_tarski @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 2.76/2.99      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.76/2.99  thf('54', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.76/2.99         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 2.76/2.99          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['52', '53'])).
% 2.76/2.99  thf('55', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]:
% 2.76/2.99         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['51', '54'])).
% 2.76/2.99  thf('56', plain,
% 2.76/2.99      (![X0 : $i, X2 : $i]:
% 2.76/2.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.76/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.76/2.99  thf('57', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]:
% 2.76/2.99         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 2.76/2.99          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 2.76/2.99      inference('sup-', [status(thm)], ['55', '56'])).
% 2.76/2.99  thf('58', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]:
% 2.76/2.99         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.76/2.99      inference('sup-', [status(thm)], ['51', '54'])).
% 2.76/2.99  thf('59', plain,
% 2.76/2.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.76/2.99      inference('demod', [status(thm)], ['57', '58'])).
% 2.76/2.99  thf('60', plain,
% 2.76/2.99      ((r1_tarski @ 
% 2.76/2.99        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 2.76/2.99        (k3_relat_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['50', '59'])).
% 2.76/2.99  thf('61', plain,
% 2.76/2.99      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 2.76/2.99        | ~ (v1_relat_1 @ sk_A))),
% 2.76/2.99      inference('sup+', [status(thm)], ['1', '60'])).
% 2.76/2.99  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 2.76/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.76/2.99  thf('63', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 2.76/2.99      inference('demod', [status(thm)], ['61', '62'])).
% 2.76/2.99  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 2.76/2.99  
% 2.76/2.99  % SZS output end Refutation
% 2.76/2.99  
% 2.86/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
