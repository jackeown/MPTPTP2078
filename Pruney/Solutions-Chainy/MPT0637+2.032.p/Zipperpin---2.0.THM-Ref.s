%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jnVy0jakR5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:00 EST 2020

% Result     : Theorem 4.49s
% Output     : Refutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  174 (1163 expanded)
%              Number of leaves         :   24 ( 412 expanded)
%              Depth                    :   22
%              Number of atoms          : 1647 (10631 expanded)
%              Number of equality atoms :   98 ( 776 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X29 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X20 @ X21 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('28',plain,(
    ! [X31: $i] :
      ( ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
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

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','47'])).

thf('49',plain,(
    ! [X31: $i] :
      ( ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('53',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('54',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','64'])).

thf('66',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('67',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k5_relat_1 @ X23 @ ( k5_relat_1 @ X22 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('76',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('79',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X20 @ X21 )
        = ( k7_relat_1 @ X20 @ ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('84',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('88',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('89',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('93',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('97',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('101',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('102',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('103',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['101','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('114',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('120',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','112','113','114','115','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['77','94','122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','124'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('126',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','124'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('132',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['135','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','129','144','145'])).

thf('147',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','146'])).

thf('148',plain,(
    $false ),
    inference(simplify,[status(thm)],['147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jnVy0jakR5
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.49/4.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.49/4.72  % Solved by: fo/fo7.sh
% 4.49/4.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.49/4.72  % done 4815 iterations in 4.255s
% 4.49/4.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.49/4.72  % SZS output start Refutation
% 4.49/4.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.49/4.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.49/4.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.49/4.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.49/4.72  thf(sk_A_type, type, sk_A: $i).
% 4.49/4.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.49/4.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.49/4.72  thf(sk_B_type, type, sk_B: $i).
% 4.49/4.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.49/4.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.49/4.72  thf(t94_relat_1, axiom,
% 4.49/4.72    (![A:$i,B:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ B ) =>
% 4.49/4.72       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 4.49/4.72  thf('0', plain,
% 4.49/4.72      (![X32 : $i, X33 : $i]:
% 4.49/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.49/4.72          | ~ (v1_relat_1 @ X33))),
% 4.49/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.49/4.72  thf(t43_funct_1, conjecture,
% 4.49/4.72    (![A:$i,B:$i]:
% 4.49/4.72     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 4.49/4.72       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.49/4.72  thf(zf_stmt_0, negated_conjecture,
% 4.49/4.72    (~( ![A:$i,B:$i]:
% 4.49/4.72        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 4.49/4.72          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 4.49/4.72    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 4.49/4.72  thf('1', plain,
% 4.49/4.72      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 4.49/4.72         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 4.49/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.49/4.72  thf('2', plain,
% 4.49/4.72      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 4.49/4.72          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 4.49/4.72        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 4.49/4.72      inference('sup-', [status(thm)], ['0', '1'])).
% 4.49/4.72  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 4.49/4.72  thf('3', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('4', plain,
% 4.49/4.72      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 4.49/4.72         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 4.49/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.49/4.72  thf('5', plain,
% 4.49/4.72      (![X32 : $i, X33 : $i]:
% 4.49/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.49/4.72          | ~ (v1_relat_1 @ X33))),
% 4.49/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.49/4.72  thf(t17_xboole_1, axiom,
% 4.49/4.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.49/4.72  thf('6', plain,
% 4.49/4.72      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 4.49/4.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.49/4.72  thf(t71_relat_1, axiom,
% 4.49/4.72    (![A:$i]:
% 4.49/4.72     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.49/4.72       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.49/4.72  thf('7', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 4.49/4.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.49/4.72  thf(t77_relat_1, axiom,
% 4.49/4.72    (![A:$i,B:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ B ) =>
% 4.49/4.72       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 4.49/4.72         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 4.49/4.72  thf('8', plain,
% 4.49/4.72      (![X29 : $i, X30 : $i]:
% 4.49/4.72         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 4.49/4.72          | ((k5_relat_1 @ (k6_relat_1 @ X30) @ X29) = (X29))
% 4.49/4.72          | ~ (v1_relat_1 @ X29))),
% 4.49/4.72      inference('cnf', [status(esa)], [t77_relat_1])).
% 4.49/4.72  thf('9', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (~ (r1_tarski @ X0 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 4.49/4.72              = (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('sup-', [status(thm)], ['7', '8'])).
% 4.49/4.72  thf('10', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('11', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (~ (r1_tarski @ X0 @ X1)
% 4.49/4.72          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 4.49/4.72              = (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('demod', [status(thm)], ['9', '10'])).
% 4.49/4.72  thf('12', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 4.49/4.72           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 4.49/4.72           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.49/4.72      inference('sup-', [status(thm)], ['6', '11'])).
% 4.49/4.72  thf('13', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 4.49/4.72            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 4.49/4.72      inference('sup+', [status(thm)], ['5', '12'])).
% 4.49/4.72  thf('14', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('15', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 4.49/4.72           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.49/4.72      inference('demod', [status(thm)], ['13', '14'])).
% 4.49/4.72  thf(t100_relat_1, axiom,
% 4.49/4.72    (![A:$i,B:$i,C:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ C ) =>
% 4.49/4.72       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 4.49/4.72         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 4.49/4.72  thf('16', plain,
% 4.49/4.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.49/4.72         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 4.49/4.72            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 4.49/4.72          | ~ (v1_relat_1 @ X17))),
% 4.49/4.72      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.49/4.72  thf(commutativity_k3_xboole_0, axiom,
% 4.49/4.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.49/4.72  thf('17', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.49/4.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.49/4.72  thf('18', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 4.49/4.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.49/4.72  thf(t192_relat_1, axiom,
% 4.49/4.72    (![A:$i,B:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ B ) =>
% 4.49/4.72       ( ( k7_relat_1 @ B @ A ) =
% 4.49/4.72         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 4.49/4.72  thf('19', plain,
% 4.49/4.72      (![X20 : $i, X21 : $i]:
% 4.49/4.72         (((k7_relat_1 @ X20 @ X21)
% 4.49/4.72            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21)))
% 4.49/4.72          | ~ (v1_relat_1 @ X20))),
% 4.49/4.72      inference('cnf', [status(esa)], [t192_relat_1])).
% 4.49/4.72  thf('20', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.49/4.72            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['18', '19'])).
% 4.49/4.72  thf('21', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('22', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.49/4.72           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 4.49/4.72      inference('demod', [status(thm)], ['20', '21'])).
% 4.49/4.72  thf('23', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.49/4.72           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['17', '22'])).
% 4.49/4.72  thf('24', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.49/4.72            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['16', '23'])).
% 4.49/4.72  thf('25', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('26', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.49/4.72           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 4.49/4.72      inference('demod', [status(thm)], ['24', '25'])).
% 4.49/4.72  thf('27', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 4.49/4.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.49/4.72  thf(t80_relat_1, axiom,
% 4.49/4.72    (![A:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ A ) =>
% 4.49/4.72       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 4.49/4.72  thf('28', plain,
% 4.49/4.72      (![X31 : $i]:
% 4.49/4.72         (((k5_relat_1 @ X31 @ (k6_relat_1 @ (k2_relat_1 @ X31))) = (X31))
% 4.49/4.72          | ~ (v1_relat_1 @ X31))),
% 4.49/4.72      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.49/4.72  thf('29', plain,
% 4.49/4.72      (![X0 : $i]:
% 4.49/4.72         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 4.49/4.72            = (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['27', '28'])).
% 4.49/4.72  thf('30', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('31', plain,
% 4.49/4.72      (![X0 : $i]:
% 4.49/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 4.49/4.72           = (k6_relat_1 @ X0))),
% 4.49/4.72      inference('demod', [status(thm)], ['29', '30'])).
% 4.49/4.72  thf('32', plain,
% 4.49/4.72      (![X32 : $i, X33 : $i]:
% 4.49/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.49/4.72          | ~ (v1_relat_1 @ X33))),
% 4.49/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.49/4.72  thf(t55_relat_1, axiom,
% 4.49/4.72    (![A:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ A ) =>
% 4.49/4.72       ( ![B:$i]:
% 4.49/4.72         ( ( v1_relat_1 @ B ) =>
% 4.49/4.72           ( ![C:$i]:
% 4.49/4.72             ( ( v1_relat_1 @ C ) =>
% 4.49/4.72               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 4.49/4.72                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 4.49/4.72  thf('33', plain,
% 4.49/4.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X22)
% 4.49/4.72          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 4.49/4.72              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 4.49/4.72          | ~ (v1_relat_1 @ X24)
% 4.49/4.72          | ~ (v1_relat_1 @ X23))),
% 4.49/4.72      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.49/4.72  thf('34', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.49/4.72            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X1))),
% 4.49/4.72      inference('sup+', [status(thm)], ['32', '33'])).
% 4.49/4.72  thf('35', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('36', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.49/4.72            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X1))),
% 4.49/4.72      inference('demod', [status(thm)], ['34', '35'])).
% 4.49/4.72  thf('37', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.49/4.72              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.49/4.72      inference('simplify', [status(thm)], ['36'])).
% 4.49/4.72  thf('38', plain,
% 4.49/4.72      (![X0 : $i]:
% 4.49/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 4.49/4.72           = (k6_relat_1 @ X0))),
% 4.49/4.72      inference('demod', [status(thm)], ['29', '30'])).
% 4.49/4.72  thf('39', plain,
% 4.49/4.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X22)
% 4.49/4.72          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 4.49/4.72              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 4.49/4.72          | ~ (v1_relat_1 @ X24)
% 4.49/4.72          | ~ (v1_relat_1 @ X23))),
% 4.49/4.72      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.49/4.72  thf(dt_k5_relat_1, axiom,
% 4.49/4.72    (![A:$i,B:$i]:
% 4.49/4.72     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 4.49/4.72       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 4.49/4.72  thf('40', plain,
% 4.49/4.72      (![X14 : $i, X15 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X14)
% 4.49/4.72          | ~ (v1_relat_1 @ X15)
% 4.49/4.72          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 4.49/4.72  thf('41', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X0)
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ X0)
% 4.49/4.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['39', '40'])).
% 4.49/4.72  thf('42', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ X0)
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 4.49/4.72      inference('simplify', [status(thm)], ['41'])).
% 4.49/4.72  thf('43', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | (v1_relat_1 @ 
% 4.49/4.72             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 4.49/4.72              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('sup-', [status(thm)], ['38', '42'])).
% 4.49/4.72  thf('44', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('45', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('46', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('47', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((v1_relat_1 @ 
% 4.49/4.72           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 4.49/4.72            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 4.49/4.72          | ~ (v1_relat_1 @ X1))),
% 4.49/4.72      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 4.49/4.72  thf('48', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((v1_relat_1 @ 
% 4.49/4.72           (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 4.49/4.72          | ~ (v1_relat_1 @ X0)
% 4.49/4.72          | ~ (v1_relat_1 @ X0))),
% 4.49/4.72      inference('sup+', [status(thm)], ['37', '47'])).
% 4.49/4.72  thf('49', plain,
% 4.49/4.72      (![X31 : $i]:
% 4.49/4.72         (((k5_relat_1 @ X31 @ (k6_relat_1 @ (k2_relat_1 @ X31))) = (X31))
% 4.49/4.72          | ~ (v1_relat_1 @ X31))),
% 4.49/4.72      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.49/4.72  thf('50', plain,
% 4.49/4.72      (![X32 : $i, X33 : $i]:
% 4.49/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.49/4.72          | ~ (v1_relat_1 @ X33))),
% 4.49/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.49/4.72  thf('51', plain,
% 4.49/4.72      (![X0 : $i]:
% 4.49/4.72         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 4.49/4.72            = (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 4.49/4.72      inference('sup+', [status(thm)], ['49', '50'])).
% 4.49/4.72  thf('52', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 4.49/4.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.49/4.72  thf('53', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('54', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 4.49/4.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.49/4.72  thf('55', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('56', plain,
% 4.49/4.72      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 4.49/4.72      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 4.49/4.72  thf('57', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('58', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ X0)
% 4.49/4.72          | ~ (v1_relat_1 @ X0))),
% 4.49/4.72      inference('demod', [status(thm)], ['48', '56', '57'])).
% 4.49/4.72  thf('59', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X0)
% 4.49/4.72          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.49/4.72      inference('simplify', [status(thm)], ['58'])).
% 4.49/4.72  thf('60', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ X0)
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 4.49/4.72      inference('simplify', [status(thm)], ['41'])).
% 4.49/4.72  thf('61', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X0)
% 4.49/4.72          | (v1_relat_1 @ 
% 4.49/4.72             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X0))),
% 4.49/4.72      inference('sup-', [status(thm)], ['59', '60'])).
% 4.49/4.72  thf('62', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('63', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X0)
% 4.49/4.72          | (v1_relat_1 @ 
% 4.49/4.72             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X0))),
% 4.49/4.72      inference('demod', [status(thm)], ['61', '62'])).
% 4.49/4.72  thf('64', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X2)
% 4.49/4.72          | (v1_relat_1 @ 
% 4.49/4.72             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 4.49/4.72          | ~ (v1_relat_1 @ X0))),
% 4.49/4.72      inference('simplify', [status(thm)], ['63'])).
% 4.49/4.72  thf('65', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['31', '64'])).
% 4.49/4.72  thf('66', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('67', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('68', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i]:
% 4.49/4.72         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 4.49/4.72      inference('demod', [status(thm)], ['65', '66', '67'])).
% 4.49/4.72  thf('69', plain,
% 4.49/4.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ X22)
% 4.49/4.72          | ((k5_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 4.49/4.72              = (k5_relat_1 @ X23 @ (k5_relat_1 @ X22 @ X24)))
% 4.49/4.72          | ~ (v1_relat_1 @ X24)
% 4.49/4.72          | ~ (v1_relat_1 @ X23))),
% 4.49/4.72      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.49/4.72  thf(t76_relat_1, axiom,
% 4.49/4.72    (![A:$i,B:$i]:
% 4.49/4.72     ( ( v1_relat_1 @ B ) =>
% 4.49/4.72       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 4.49/4.72         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 4.49/4.72  thf('70', plain,
% 4.49/4.72      (![X27 : $i, X28 : $i]:
% 4.49/4.72         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 4.49/4.72          | ~ (v1_relat_1 @ X27))),
% 4.49/4.72      inference('cnf', [status(esa)], [t76_relat_1])).
% 4.49/4.72  thf('71', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         ((r1_tarski @ 
% 4.49/4.72           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 4.49/4.72           (k5_relat_1 @ X2 @ X1))
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 4.49/4.72      inference('sup+', [status(thm)], ['69', '70'])).
% 4.49/4.72  thf('72', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('73', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         ((r1_tarski @ 
% 4.49/4.72           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 4.49/4.72           (k5_relat_1 @ X2 @ X1))
% 4.49/4.72          | ~ (v1_relat_1 @ X2)
% 4.49/4.72          | ~ (v1_relat_1 @ X1)
% 4.49/4.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 4.49/4.72      inference('demod', [status(thm)], ['71', '72'])).
% 4.49/4.72  thf('74', plain,
% 4.49/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.49/4.72         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.49/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 4.49/4.72          | (r1_tarski @ 
% 4.49/4.72             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 4.49/4.72              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 4.49/4.72             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 4.49/4.72      inference('sup-', [status(thm)], ['68', '73'])).
% 4.49/4.72  thf('75', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.49/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.49/4.72  thf('76', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('77', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (r1_tarski @ 
% 4.56/4.72          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 4.56/4.72           (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 4.56/4.72          (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 4.56/4.72      inference('demod', [status(thm)], ['74', '75', '76'])).
% 4.56/4.72  thf('78', plain,
% 4.56/4.72      (![X32 : $i, X33 : $i]:
% 4.56/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.56/4.72          | ~ (v1_relat_1 @ X33))),
% 4.56/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.56/4.72  thf('79', plain,
% 4.56/4.72      (![X20 : $i, X21 : $i]:
% 4.56/4.72         (((k7_relat_1 @ X20 @ X21)
% 4.56/4.72            = (k7_relat_1 @ X20 @ (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21)))
% 4.56/4.72          | ~ (v1_relat_1 @ X20))),
% 4.56/4.72      inference('cnf', [status(esa)], [t192_relat_1])).
% 4.56/4.72  thf('80', plain,
% 4.56/4.72      (![X0 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 4.56/4.72           = (k6_relat_1 @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['29', '30'])).
% 4.56/4.72  thf('81', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X2)
% 4.56/4.72          | ~ (v1_relat_1 @ X1)
% 4.56/4.72          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.56/4.72              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.56/4.72      inference('simplify', [status(thm)], ['36'])).
% 4.56/4.72  thf('82', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 4.56/4.72            (k6_relat_1 @ X0))
% 4.56/4.72            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['80', '81'])).
% 4.56/4.72  thf('83', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('84', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('85', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 4.56/4.72           (k6_relat_1 @ X0))
% 4.56/4.72           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 4.56/4.72      inference('demod', [status(thm)], ['82', '83', '84'])).
% 4.56/4.72  thf('86', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 4.56/4.72            (k6_relat_1 @ X1))
% 4.56/4.72            = (k5_relat_1 @ 
% 4.56/4.72               (k6_relat_1 @ 
% 4.56/4.72                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 4.56/4.72               (k6_relat_1 @ X1)))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['79', '85'])).
% 4.56/4.72  thf('87', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 4.56/4.72           (k6_relat_1 @ X0))
% 4.56/4.72           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 4.56/4.72      inference('demod', [status(thm)], ['82', '83', '84'])).
% 4.56/4.72  thf('88', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 4.56/4.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.56/4.72  thf('89', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('90', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 4.56/4.72              (k6_relat_1 @ X1)))),
% 4.56/4.72      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 4.56/4.72  thf('91', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['78', '90'])).
% 4.56/4.72  thf('92', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 4.56/4.72      inference('demod', [status(thm)], ['20', '21'])).
% 4.56/4.72  thf('93', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('94', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.56/4.72  thf('95', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.56/4.72  thf('96', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X2)
% 4.56/4.72          | ~ (v1_relat_1 @ X1)
% 4.56/4.72          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.56/4.72              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.56/4.72      inference('simplify', [status(thm)], ['36'])).
% 4.56/4.72  thf('97', plain,
% 4.56/4.72      (![X32 : $i, X33 : $i]:
% 4.56/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.56/4.72          | ~ (v1_relat_1 @ X33))),
% 4.56/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.56/4.72  thf('98', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 4.56/4.72            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ X2)
% 4.56/4.72          | ~ (v1_relat_1 @ X0)
% 4.56/4.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['96', '97'])).
% 4.56/4.72  thf('99', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.56/4.72          | ((k7_relat_1 @ 
% 4.56/4.72              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ X2)
% 4.56/4.72              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 4.56/4.72                 (k6_relat_1 @ X1))))),
% 4.56/4.72      inference('sup-', [status(thm)], ['95', '98'])).
% 4.56/4.72  thf('100', plain,
% 4.56/4.72      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 4.56/4.72  thf('101', plain,
% 4.56/4.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 4.56/4.72            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 4.56/4.72          | ~ (v1_relat_1 @ X17))),
% 4.56/4.72      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.56/4.72  thf('102', plain,
% 4.56/4.72      (![X32 : $i, X33 : $i]:
% 4.56/4.72         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 4.56/4.72          | ~ (v1_relat_1 @ X33))),
% 4.56/4.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.56/4.72  thf('103', plain,
% 4.56/4.72      (![X14 : $i, X15 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X14)
% 4.56/4.72          | ~ (v1_relat_1 @ X15)
% 4.56/4.72          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 4.56/4.72  thf('104', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ X1)
% 4.56/4.72          | ~ (v1_relat_1 @ X1)
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['102', '103'])).
% 4.56/4.72  thf('105', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('106', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ X1)
% 4.56/4.72          | ~ (v1_relat_1 @ X1))),
% 4.56/4.72      inference('demod', [status(thm)], ['104', '105'])).
% 4.56/4.72  thf('107', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 4.56/4.72      inference('simplify', [status(thm)], ['106'])).
% 4.56/4.72  thf('108', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ X2)
% 4.56/4.72          | ~ (v1_relat_1 @ X2))),
% 4.56/4.72      inference('sup+', [status(thm)], ['101', '107'])).
% 4.56/4.72  thf('109', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X2)
% 4.56/4.72          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 4.56/4.72      inference('simplify', [status(thm)], ['108'])).
% 4.56/4.72  thf('110', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['100', '109'])).
% 4.56/4.72  thf('111', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('112', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 4.56/4.72      inference('demod', [status(thm)], ['110', '111'])).
% 4.56/4.72  thf('113', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('114', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('115', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.56/4.72  thf('116', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.56/4.72  thf('117', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X2)
% 4.56/4.72          | ~ (v1_relat_1 @ X1)
% 4.56/4.72          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.56/4.72              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.56/4.72      inference('simplify', [status(thm)], ['36'])).
% 4.56/4.72  thf('118', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 4.56/4.72            (k6_relat_1 @ X1))
% 4.56/4.72            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 4.56/4.72               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['116', '117'])).
% 4.56/4.72  thf('119', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('120', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('121', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 4.56/4.72           (k6_relat_1 @ X1))
% 4.56/4.72           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 4.56/4.72              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.56/4.72      inference('demod', [status(thm)], ['118', '119', '120'])).
% 4.56/4.72  thf('122', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 4.56/4.72           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 4.56/4.72              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.56/4.72      inference('demod', [status(thm)],
% 4.56/4.72                ['99', '112', '113', '114', '115', '121'])).
% 4.56/4.72  thf('123', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.56/4.72  thf('124', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (r1_tarski @ 
% 4.56/4.72          (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1) @ 
% 4.56/4.72          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 4.56/4.72      inference('demod', [status(thm)], ['77', '94', '122', '123'])).
% 4.56/4.72  thf('125', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 4.56/4.72          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 4.56/4.72      inference('sup+', [status(thm)], ['26', '124'])).
% 4.56/4.72  thf(d10_xboole_0, axiom,
% 4.56/4.72    (![A:$i,B:$i]:
% 4.56/4.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.56/4.72  thf('126', plain,
% 4.56/4.72      (![X2 : $i, X4 : $i]:
% 4.56/4.72         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.56/4.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.56/4.72  thf('127', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 4.56/4.72             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 4.56/4.72          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 4.56/4.72              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 4.56/4.72      inference('sup-', [status(thm)], ['125', '126'])).
% 4.56/4.72  thf('128', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 4.56/4.72          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 4.56/4.72      inference('sup+', [status(thm)], ['26', '124'])).
% 4.56/4.72  thf('129', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 4.56/4.72           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 4.56/4.72      inference('demod', [status(thm)], ['127', '128'])).
% 4.56/4.72  thf('130', plain,
% 4.56/4.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 4.56/4.72            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 4.56/4.72          | ~ (v1_relat_1 @ X17))),
% 4.56/4.72      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.56/4.72  thf('131', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.56/4.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.56/4.72  thf('132', plain,
% 4.56/4.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 4.56/4.72            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 4.56/4.72          | ~ (v1_relat_1 @ X17))),
% 4.56/4.72      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.56/4.72  thf('133', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 4.56/4.72            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 4.56/4.72          | ~ (v1_relat_1 @ X2))),
% 4.56/4.72      inference('sup+', [status(thm)], ['131', '132'])).
% 4.56/4.72  thf('134', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 4.56/4.72            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ X2)
% 4.56/4.72          | ~ (v1_relat_1 @ X2))),
% 4.56/4.72      inference('sup+', [status(thm)], ['130', '133'])).
% 4.56/4.72  thf('135', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (~ (v1_relat_1 @ X2)
% 4.56/4.72          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 4.56/4.72              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 4.56/4.72      inference('simplify', [status(thm)], ['134'])).
% 4.56/4.72  thf('136', plain,
% 4.56/4.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 4.56/4.72            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 4.56/4.72          | ~ (v1_relat_1 @ X17))),
% 4.56/4.72      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.56/4.72  thf('137', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.56/4.72           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['24', '25'])).
% 4.56/4.72  thf('138', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 4.56/4.72            = (k7_relat_1 @ 
% 4.56/4.72               (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))
% 4.56/4.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['136', '137'])).
% 4.56/4.72  thf('139', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 4.56/4.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 4.56/4.72  thf('140', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 4.56/4.72           = (k7_relat_1 @ 
% 4.56/4.72              (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ X2))),
% 4.56/4.72      inference('demod', [status(thm)], ['138', '139'])).
% 4.56/4.72  thf('141', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 4.56/4.72            = (k7_relat_1 @ 
% 4.56/4.72               (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X1) @ X0))
% 4.56/4.72          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2)))),
% 4.56/4.72      inference('sup+', [status(thm)], ['135', '140'])).
% 4.56/4.72  thf('142', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.56/4.72           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['24', '25'])).
% 4.56/4.72  thf('143', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 4.56/4.72      inference('demod', [status(thm)], ['110', '111'])).
% 4.56/4.72  thf('144', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 4.56/4.72           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X2) @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['141', '142', '143'])).
% 4.56/4.72  thf('145', plain,
% 4.56/4.72      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 4.56/4.72      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 4.56/4.72  thf('146', plain,
% 4.56/4.72      (![X0 : $i, X1 : $i]:
% 4.56/4.72         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 4.56/4.72           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.56/4.72      inference('demod', [status(thm)], ['15', '129', '144', '145'])).
% 4.56/4.72  thf('147', plain,
% 4.56/4.72      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 4.56/4.72         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 4.56/4.72      inference('demod', [status(thm)], ['4', '146'])).
% 4.56/4.72  thf('148', plain, ($false), inference('simplify', [status(thm)], ['147'])).
% 4.56/4.72  
% 4.56/4.72  % SZS output end Refutation
% 4.56/4.72  
% 4.56/4.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
