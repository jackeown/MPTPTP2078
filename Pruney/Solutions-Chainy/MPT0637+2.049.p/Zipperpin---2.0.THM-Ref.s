%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U5G0NhrRcY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:02 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  179 (1898 expanded)
%              Number of leaves         :   25 ( 673 expanded)
%              Depth                    :   21
%              Number of atoms          : 1691 (17795 expanded)
%              Number of equality atoms :  118 (1203 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( ( ( k5_relat_1 @ X28 @ ( k6_relat_1 @ ( k2_relat_1 @ X28 ) ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('11',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X28: $i] :
      ( ( ( k5_relat_1 @ X28 @ ( k6_relat_1 @ ( k2_relat_1 @ X28 ) ) )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','40'])).

thf('42',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('48',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('53',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('62',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('72',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','58','59','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','37','38','39'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('80',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','37','38','39'])).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('90',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X24 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('98',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('101',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X22 @ ( k6_relat_1 @ X23 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','105'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','105'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('114',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('119',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('121',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X24 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','126'])).

thf('128',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('130',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('131',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('132',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('133',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ( ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','37','38','39'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','144','145'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','150'])).

thf('152',plain,(
    $false ),
    inference(simplify,[status(thm)],['151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U5G0NhrRcY
% 0.16/0.36  % Computer   : n005.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 11:20:03 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 1.44/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.44/1.64  % Solved by: fo/fo7.sh
% 1.44/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.64  % done 1579 iterations in 1.159s
% 1.44/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.44/1.64  % SZS output start Refutation
% 1.44/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.44/1.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.44/1.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.44/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.44/1.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.44/1.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.44/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.44/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.44/1.64  thf(t94_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.44/1.64  thf('0', plain,
% 1.44/1.64      (![X31 : $i, X32 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.44/1.64          | ~ (v1_relat_1 @ X32))),
% 1.44/1.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.44/1.64  thf(t43_funct_1, conjecture,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.44/1.64       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.44/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.64    (~( ![A:$i,B:$i]:
% 1.44/1.64        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.44/1.64          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.44/1.64    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 1.44/1.64  thf('1', plain,
% 1.44/1.64      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.44/1.64         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('2', plain,
% 1.44/1.64      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 1.44/1.64          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 1.44/1.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['0', '1'])).
% 1.44/1.64  thf(fc3_funct_1, axiom,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.44/1.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.44/1.64  thf('3', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('4', plain,
% 1.44/1.64      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 1.44/1.64         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.44/1.64      inference('demod', [status(thm)], ['2', '3'])).
% 1.44/1.64  thf(t80_relat_1, axiom,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ A ) =>
% 1.44/1.64       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.44/1.64  thf('5', plain,
% 1.44/1.64      (![X28 : $i]:
% 1.44/1.64         (((k5_relat_1 @ X28 @ (k6_relat_1 @ (k2_relat_1 @ X28))) = (X28))
% 1.44/1.64          | ~ (v1_relat_1 @ X28))),
% 1.44/1.64      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.44/1.64  thf('6', plain,
% 1.44/1.64      (![X31 : $i, X32 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.44/1.64          | ~ (v1_relat_1 @ X32))),
% 1.44/1.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.44/1.64  thf('7', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 1.44/1.64            = (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 1.44/1.64      inference('sup+', [status(thm)], ['5', '6'])).
% 1.44/1.64  thf(t71_relat_1, axiom,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.44/1.64       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.44/1.64  thf('8', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('9', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('10', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('11', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('12', plain,
% 1.44/1.64      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.44/1.64  thf('13', plain,
% 1.44/1.64      (![X31 : $i, X32 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.44/1.64          | ~ (v1_relat_1 @ X32))),
% 1.44/1.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.44/1.64  thf(t112_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ![C:$i]:
% 1.44/1.64         ( ( v1_relat_1 @ C ) =>
% 1.44/1.64           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.44/1.64             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 1.44/1.64  thf('14', plain,
% 1.44/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X14)
% 1.44/1.64          | ((k7_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X14))
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.44/1.64  thf('15', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['13', '14'])).
% 1.44/1.64  thf('16', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('17', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['15', '16'])).
% 1.44/1.64  thf('18', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 1.44/1.64      inference('simplify', [status(thm)], ['17'])).
% 1.44/1.64  thf('19', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 1.44/1.64            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['12', '18'])).
% 1.44/1.64  thf('20', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('21', plain,
% 1.44/1.64      (![X28 : $i]:
% 1.44/1.64         (((k5_relat_1 @ X28 @ (k6_relat_1 @ (k2_relat_1 @ X28))) = (X28))
% 1.44/1.64          | ~ (v1_relat_1 @ X28))),
% 1.44/1.64      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.44/1.64  thf('22', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.44/1.64            = (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['20', '21'])).
% 1.44/1.64  thf('23', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('24', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.44/1.64           = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.44/1.64  thf('25', plain,
% 1.44/1.64      (![X31 : $i, X32 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.44/1.64          | ~ (v1_relat_1 @ X32))),
% 1.44/1.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.44/1.64  thf(t55_relat_1, axiom,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ A ) =>
% 1.44/1.64       ( ![B:$i]:
% 1.44/1.64         ( ( v1_relat_1 @ B ) =>
% 1.44/1.64           ( ![C:$i]:
% 1.44/1.64             ( ( v1_relat_1 @ C ) =>
% 1.44/1.64               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.44/1.64                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.44/1.64  thf('26', plain,
% 1.44/1.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X17)
% 1.44/1.64          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 1.44/1.64              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 1.44/1.64          | ~ (v1_relat_1 @ X19)
% 1.44/1.64          | ~ (v1_relat_1 @ X18))),
% 1.44/1.64      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.44/1.64  thf('27', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['25', '26'])).
% 1.44/1.64  thf('28', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('29', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['27', '28'])).
% 1.44/1.64  thf('30', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['29'])).
% 1.44/1.64  thf('31', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64            (k6_relat_1 @ X0))
% 1.44/1.64            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['24', '30'])).
% 1.44/1.64  thf('32', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.44/1.64           = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.44/1.64  thf('33', plain,
% 1.44/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X14)
% 1.44/1.64          | ((k7_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X14))
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.44/1.64  thf('34', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64               (k6_relat_1 @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['32', '33'])).
% 1.44/1.64  thf('35', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('36', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('37', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64              (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.44/1.64  thf('38', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('39', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('40', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['31', '37', '38', '39'])).
% 1.44/1.64  thf('41', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.44/1.64            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['19', '40'])).
% 1.44/1.64  thf('42', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('43', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.44/1.64           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['41', '42'])).
% 1.44/1.64  thf(t90_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.44/1.64         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.44/1.64  thf('44', plain,
% 1.44/1.64      (![X29 : $i, X30 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.44/1.64          | ~ (v1_relat_1 @ X29))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('45', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.44/1.64            = (k3_xboole_0 @ 
% 1.44/1.64               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['43', '44'])).
% 1.44/1.64  thf('46', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.44/1.64           = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.44/1.64  thf('47', plain,
% 1.44/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X14)
% 1.44/1.64          | ((k7_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X14))
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.44/1.64  thf('48', plain,
% 1.44/1.64      (![X29 : $i, X30 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.44/1.64          | ~ (v1_relat_1 @ X29))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('49', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X0)
% 1.44/1.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['47', '48'])).
% 1.44/1.64  thf('50', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ((k1_relat_1 @ 
% 1.44/1.64              (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64               (k6_relat_1 @ X0)))
% 1.44/1.64              = (k3_xboole_0 @ 
% 1.44/1.64                 (k1_relat_1 @ 
% 1.44/1.64                  (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))) @ 
% 1.44/1.64                 X1)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['46', '49'])).
% 1.44/1.64  thf('51', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('52', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('53', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('54', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.44/1.64           = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.44/1.64  thf('55', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('56', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k1_relat_1 @ 
% 1.44/1.64           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64            (k6_relat_1 @ X0)))
% 1.44/1.64           = (k3_xboole_0 @ X0 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['50', '51', '52', '53', '54', '55'])).
% 1.44/1.64  thf('57', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64              (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.44/1.64  thf('58', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64           = (k3_xboole_0 @ X0 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['56', '57'])).
% 1.44/1.64  thf('59', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64           = (k3_xboole_0 @ X0 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['56', '57'])).
% 1.44/1.64  thf('60', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.44/1.64           = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.44/1.64  thf('61', plain,
% 1.44/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X14)
% 1.44/1.64          | ((k7_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X14))
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.44/1.64  thf('62', plain,
% 1.44/1.64      (![X31 : $i, X32 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.44/1.64          | ~ (v1_relat_1 @ X32))),
% 1.44/1.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.44/1.64  thf(dt_k5_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.44/1.64       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.44/1.64  thf('63', plain,
% 1.44/1.64      (![X12 : $i, X13 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X12)
% 1.44/1.64          | ~ (v1_relat_1 @ X13)
% 1.44/1.64          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 1.44/1.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.44/1.64  thf('64', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['62', '63'])).
% 1.44/1.64  thf('65', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('66', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['64', '65'])).
% 1.44/1.64  thf('67', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.44/1.64      inference('simplify', [status(thm)], ['66'])).
% 1.44/1.64  thf('68', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X0)
% 1.44/1.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['61', '67'])).
% 1.44/1.64  thf('69', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | (v1_relat_1 @ 
% 1.44/1.64             (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64              (k6_relat_1 @ X0))))),
% 1.44/1.64      inference('sup-', [status(thm)], ['60', '68'])).
% 1.44/1.64  thf('70', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('71', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('72', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('73', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64              (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.44/1.64  thf('74', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 1.44/1.64  thf('75', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k3_xboole_0 @ X1 @ X0)
% 1.44/1.64           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['45', '58', '59', '74'])).
% 1.44/1.64  thf('76', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['31', '37', '38', '39'])).
% 1.44/1.64  thf('77', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['29'])).
% 1.44/1.64  thf('78', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.44/1.64            (k6_relat_1 @ X1))
% 1.44/1.64            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.44/1.64               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['76', '77'])).
% 1.44/1.64  thf('79', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('80', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('81', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.44/1.64           (k6_relat_1 @ X1))
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.44/1.64              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.44/1.64  thf('82', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['31', '37', '38', '39'])).
% 1.44/1.64  thf('83', plain,
% 1.44/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X14)
% 1.44/1.64          | ((k7_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ X15 @ X16) @ X14))
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.44/1.64  thf('84', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.44/1.64            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.44/1.64               (k6_relat_1 @ X1)))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['82', '83'])).
% 1.44/1.64  thf('85', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('86', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('87', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.44/1.64           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.44/1.64              (k6_relat_1 @ X1)))),
% 1.44/1.64      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.44/1.64  thf('88', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.44/1.64              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['81', '87'])).
% 1.44/1.64  thf(t17_xboole_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.44/1.64  thf('89', plain,
% 1.44/1.64      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.44/1.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.44/1.64  thf('90', plain,
% 1.44/1.64      (![X29 : $i, X30 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.44/1.64          | ~ (v1_relat_1 @ X29))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf(t77_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.44/1.64         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.44/1.64  thf('91', plain,
% 1.44/1.64      (![X24 : $i, X25 : $i]:
% 1.44/1.64         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ X25) @ X24) = (X24))
% 1.44/1.64          | ~ (v1_relat_1 @ X24))),
% 1.44/1.64      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.44/1.64  thf('92', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64              = (k7_relat_1 @ X1 @ X0)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['90', '91'])).
% 1.44/1.64  thf('93', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.44/1.64            (k7_relat_1 @ X0 @ X1)) = (k7_relat_1 @ X0 @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ X0))),
% 1.44/1.64      inference('sup-', [status(thm)], ['89', '92'])).
% 1.44/1.64  thf('94', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.44/1.64      inference('simplify', [status(thm)], ['66'])).
% 1.44/1.64  thf('95', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X0)
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.44/1.64              (k7_relat_1 @ X0 @ X1)) = (k7_relat_1 @ X0 @ X1)))),
% 1.44/1.64      inference('clc', [status(thm)], ['93', '94'])).
% 1.44/1.64  thf('96', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.44/1.64            (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.44/1.64            = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['88', '95'])).
% 1.44/1.64  thf('97', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('98', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('99', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.44/1.64  thf('100', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 1.44/1.64      inference('simplify', [status(thm)], ['17'])).
% 1.44/1.64  thf(t76_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.44/1.64         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.44/1.64  thf('101', plain,
% 1.44/1.64      (![X22 : $i, X23 : $i]:
% 1.44/1.64         ((r1_tarski @ (k5_relat_1 @ X22 @ (k6_relat_1 @ X23)) @ X22)
% 1.44/1.64          | ~ (v1_relat_1 @ X22))),
% 1.44/1.64      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.44/1.64  thf('102', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((r1_tarski @ 
% 1.44/1.64           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 1.44/1.64           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 1.44/1.64          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['100', '101'])).
% 1.44/1.64  thf('103', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('104', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 1.44/1.64  thf('105', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (r1_tarski @ 
% 1.44/1.64          (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 1.44/1.64          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.44/1.64  thf('106', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 1.44/1.64          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['99', '105'])).
% 1.44/1.64  thf(d10_xboole_0, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.44/1.64  thf('107', plain,
% 1.44/1.64      (![X0 : $i, X2 : $i]:
% 1.44/1.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.44/1.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.44/1.64  thf('108', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 1.44/1.64             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.44/1.64              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['106', '107'])).
% 1.44/1.64  thf('109', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 1.44/1.64          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['99', '105'])).
% 1.44/1.64  thf('110', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['108', '109'])).
% 1.44/1.64  thf('111', plain,
% 1.44/1.64      (![X29 : $i, X30 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.44/1.64          | ~ (v1_relat_1 @ X29))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('112', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['110', '111'])).
% 1.44/1.64  thf('113', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64           = (k3_xboole_0 @ X0 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['56', '57'])).
% 1.44/1.64  thf('114', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('115', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('116', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 1.44/1.64  thf('117', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k3_xboole_0 @ X1 @ X0)
% 1.44/1.64           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['75', '116'])).
% 1.44/1.64  thf('118', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['108', '109'])).
% 1.44/1.64  thf('119', plain,
% 1.44/1.64      (![X29 : $i, X30 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 1.44/1.64          | ~ (v1_relat_1 @ X29))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('120', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.44/1.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.44/1.64  thf('121', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.44/1.64      inference('simplify', [status(thm)], ['120'])).
% 1.44/1.64  thf('122', plain,
% 1.44/1.64      (![X24 : $i, X25 : $i]:
% 1.44/1.64         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ X25) @ X24) = (X24))
% 1.44/1.64          | ~ (v1_relat_1 @ X24))),
% 1.44/1.64      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.44/1.64  thf('123', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X0)
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['121', '122'])).
% 1.44/1.64  thf('124', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k5_relat_1 @ 
% 1.44/1.64            (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ 
% 1.44/1.64            (k7_relat_1 @ X1 @ X0)) = (k7_relat_1 @ X1 @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['119', '123'])).
% 1.44/1.64  thf('125', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.44/1.64      inference('simplify', [status(thm)], ['66'])).
% 1.44/1.64  thf('126', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k5_relat_1 @ 
% 1.44/1.64              (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)) @ 
% 1.44/1.64              (k7_relat_1 @ X1 @ X0)) = (k7_relat_1 @ X1 @ X0)))),
% 1.44/1.64      inference('clc', [status(thm)], ['124', '125'])).
% 1.44/1.64  thf('127', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k5_relat_1 @ 
% 1.44/1.64            (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X1)) @ 
% 1.44/1.64            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.44/1.64            = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['118', '126'])).
% 1.44/1.64  thf('128', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf('129', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.44/1.64              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['81', '87'])).
% 1.44/1.64  thf('130', plain,
% 1.44/1.64      (![X31 : $i, X32 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 1.44/1.64          | ~ (v1_relat_1 @ X32))),
% 1.44/1.64      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.44/1.64  thf('131', plain,
% 1.44/1.64      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.44/1.64      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.44/1.64  thf('132', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 1.44/1.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.44/1.64  thf(t79_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.44/1.64         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.44/1.64  thf('133', plain,
% 1.44/1.64      (![X26 : $i, X27 : $i]:
% 1.44/1.64         (~ (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 1.44/1.64          | ((k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) = (X26))
% 1.44/1.64          | ~ (v1_relat_1 @ X26))),
% 1.44/1.64      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.44/1.64  thf('134', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (r1_tarski @ X0 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 1.44/1.64              = (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['132', '133'])).
% 1.44/1.64  thf('135', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('136', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (r1_tarski @ X0 @ X1)
% 1.44/1.64          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 1.44/1.64              = (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['134', '135'])).
% 1.44/1.64  thf('137', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.44/1.64           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.44/1.64      inference('sup-', [status(thm)], ['131', '136'])).
% 1.44/1.64  thf('138', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.44/1.64            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['130', '137'])).
% 1.44/1.64  thf('139', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('140', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.44/1.64           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['138', '139'])).
% 1.44/1.64  thf('141', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.44/1.64           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.44/1.64              (k6_relat_1 @ X1)))),
% 1.44/1.64      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.44/1.64  thf('142', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ 
% 1.44/1.64           (k3_xboole_0 @ X1 @ X0))
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.44/1.64              (k6_relat_1 @ X2)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['140', '141'])).
% 1.44/1.64  thf('143', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.44/1.64           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['31', '37', '38', '39'])).
% 1.44/1.64  thf('144', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ 
% 1.44/1.64           (k3_xboole_0 @ X1 @ X0))
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['142', '143'])).
% 1.44/1.64  thf('145', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 1.44/1.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.44/1.64  thf('146', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['127', '128', '129', '144', '145'])).
% 1.44/1.64  thf('147', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.44/1.64           (k3_xboole_0 @ X1 @ X0))
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.64      inference('sup+', [status(thm)], ['117', '146'])).
% 1.44/1.64  thf('148', plain,
% 1.44/1.64      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 1.44/1.64  thf('149', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.44/1.64      inference('demod', [status(thm)], ['127', '128', '129', '144', '145'])).
% 1.44/1.64  thf('150', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.44/1.64           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['147', '148', '149'])).
% 1.44/1.64  thf('151', plain,
% 1.44/1.64      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.44/1.64         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.44/1.64      inference('demod', [status(thm)], ['4', '150'])).
% 1.44/1.64  thf('152', plain, ($false), inference('simplify', [status(thm)], ['151'])).
% 1.44/1.64  
% 1.44/1.64  % SZS output end Refutation
% 1.44/1.64  
% 1.44/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
