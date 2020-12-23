%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XUD2gMiDy4

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:02 EST 2020

% Result     : Theorem 6.35s
% Output     : Refutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :  155 (1790 expanded)
%              Number of leaves         :   22 ( 631 expanded)
%              Depth                    :   25
%              Number of atoms          : 1500 (16477 expanded)
%              Number of equality atoms :   94 (1235 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
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
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('18',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('21',plain,(
    ! [X30: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X30 ) ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

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
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('37',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','39'])).

thf('41',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k7_relat_1 @ X19 @ ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('48',plain,(
    ! [X30: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X30 ) ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('56',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','59'])).

thf('61',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('63',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k5_relat_1 @ X22 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('101',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('106',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('110',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('111',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','121'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('123',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','121'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','129'])).

thf('131',plain,(
    $false ),
    inference(simplify,[status(thm)],['130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XUD2gMiDy4
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.35/6.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.35/6.58  % Solved by: fo/fo7.sh
% 6.35/6.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.35/6.58  % done 5081 iterations in 6.125s
% 6.35/6.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.35/6.58  % SZS output start Refutation
% 6.35/6.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.35/6.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.35/6.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.35/6.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.35/6.58  thf(sk_A_type, type, sk_A: $i).
% 6.35/6.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.35/6.58  thf(sk_B_type, type, sk_B: $i).
% 6.35/6.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.35/6.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.35/6.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.35/6.58  thf(t94_relat_1, axiom,
% 6.35/6.58    (![A:$i,B:$i]:
% 6.35/6.58     ( ( v1_relat_1 @ B ) =>
% 6.35/6.58       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 6.35/6.58  thf('0', plain,
% 6.35/6.58      (![X32 : $i, X33 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.58          | ~ (v1_relat_1 @ X33))),
% 6.35/6.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.58  thf(t43_funct_1, conjecture,
% 6.35/6.58    (![A:$i,B:$i]:
% 6.35/6.58     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 6.35/6.58       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.35/6.58  thf(zf_stmt_0, negated_conjecture,
% 6.35/6.58    (~( ![A:$i,B:$i]:
% 6.35/6.58        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 6.35/6.58          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 6.35/6.58    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 6.35/6.58  thf('1', plain,
% 6.35/6.58      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 6.35/6.58         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 6.35/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.35/6.58  thf('2', plain,
% 6.35/6.58      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.35/6.58          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 6.35/6.58        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 6.35/6.58      inference('sup-', [status(thm)], ['0', '1'])).
% 6.35/6.58  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 6.35/6.58  thf('3', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('4', plain,
% 6.35/6.58      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.35/6.58         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 6.35/6.58      inference('demod', [status(thm)], ['2', '3'])).
% 6.35/6.58  thf('5', plain,
% 6.35/6.58      (![X32 : $i, X33 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.58          | ~ (v1_relat_1 @ X33))),
% 6.35/6.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.58  thf(t17_xboole_1, axiom,
% 6.35/6.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.35/6.58  thf('6', plain,
% 6.35/6.58      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 6.35/6.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.35/6.58  thf(t71_relat_1, axiom,
% 6.35/6.58    (![A:$i]:
% 6.35/6.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.35/6.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.35/6.58  thf('7', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.58  thf(t77_relat_1, axiom,
% 6.35/6.58    (![A:$i,B:$i]:
% 6.35/6.58     ( ( v1_relat_1 @ B ) =>
% 6.35/6.58       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 6.35/6.58         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 6.35/6.58  thf('8', plain,
% 6.35/6.58      (![X28 : $i, X29 : $i]:
% 6.35/6.58         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 6.35/6.58          | ((k5_relat_1 @ (k6_relat_1 @ X29) @ X28) = (X28))
% 6.35/6.58          | ~ (v1_relat_1 @ X28))),
% 6.35/6.58      inference('cnf', [status(esa)], [t77_relat_1])).
% 6.35/6.58  thf('9', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         (~ (r1_tarski @ X0 @ X1)
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.58          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 6.35/6.58              = (k6_relat_1 @ X0)))),
% 6.35/6.58      inference('sup-', [status(thm)], ['7', '8'])).
% 6.35/6.58  thf('10', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('11', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         (~ (r1_tarski @ X0 @ X1)
% 6.35/6.58          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 6.35/6.58              = (k6_relat_1 @ X0)))),
% 6.35/6.58      inference('demod', [status(thm)], ['9', '10'])).
% 6.35/6.58  thf('12', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 6.35/6.58           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 6.35/6.58           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.58      inference('sup-', [status(thm)], ['6', '11'])).
% 6.35/6.58  thf('13', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 6.35/6.58            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 6.35/6.58      inference('sup+', [status(thm)], ['5', '12'])).
% 6.35/6.58  thf('14', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('15', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 6.35/6.58           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.58      inference('demod', [status(thm)], ['13', '14'])).
% 6.35/6.58  thf('16', plain,
% 6.35/6.58      (![X32 : $i, X33 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.58          | ~ (v1_relat_1 @ X33))),
% 6.35/6.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.58  thf(t192_relat_1, axiom,
% 6.35/6.58    (![A:$i,B:$i]:
% 6.35/6.58     ( ( v1_relat_1 @ B ) =>
% 6.35/6.58       ( ( k7_relat_1 @ B @ A ) =
% 6.35/6.58         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 6.35/6.58  thf('17', plain,
% 6.35/6.58      (![X19 : $i, X20 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X19 @ X20)
% 6.35/6.58            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.35/6.58          | ~ (v1_relat_1 @ X19))),
% 6.35/6.58      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.35/6.58  thf('18', plain,
% 6.35/6.58      (![X32 : $i, X33 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.58          | ~ (v1_relat_1 @ X33))),
% 6.35/6.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.58  thf('19', plain,
% 6.35/6.58      (![X19 : $i, X20 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X19 @ X20)
% 6.35/6.58            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.35/6.58          | ~ (v1_relat_1 @ X19))),
% 6.35/6.58      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.35/6.58  thf('20', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.58  thf(t78_relat_1, axiom,
% 6.35/6.58    (![A:$i]:
% 6.35/6.58     ( ( v1_relat_1 @ A ) =>
% 6.35/6.58       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 6.35/6.58  thf('21', plain,
% 6.35/6.58      (![X30 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X30)) @ X30) = (X30))
% 6.35/6.58          | ~ (v1_relat_1 @ X30))),
% 6.35/6.58      inference('cnf', [status(esa)], [t78_relat_1])).
% 6.35/6.58  thf('22', plain,
% 6.35/6.58      (![X0 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 6.35/6.58            = (k6_relat_1 @ X0))
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.35/6.58      inference('sup+', [status(thm)], ['20', '21'])).
% 6.35/6.58  thf('23', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('24', plain,
% 6.35/6.58      (![X0 : $i]:
% 6.35/6.58         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 6.35/6.58           = (k6_relat_1 @ X0))),
% 6.35/6.58      inference('demod', [status(thm)], ['22', '23'])).
% 6.35/6.58  thf('25', plain,
% 6.35/6.58      (![X32 : $i, X33 : $i]:
% 6.35/6.58         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.58          | ~ (v1_relat_1 @ X33))),
% 6.35/6.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.58  thf(t55_relat_1, axiom,
% 6.35/6.58    (![A:$i]:
% 6.35/6.58     ( ( v1_relat_1 @ A ) =>
% 6.35/6.58       ( ![B:$i]:
% 6.35/6.58         ( ( v1_relat_1 @ B ) =>
% 6.35/6.58           ( ![C:$i]:
% 6.35/6.58             ( ( v1_relat_1 @ C ) =>
% 6.35/6.58               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 6.35/6.58                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 6.35/6.58  thf('26', plain,
% 6.35/6.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.35/6.58         (~ (v1_relat_1 @ X21)
% 6.35/6.58          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 6.35/6.58              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 6.35/6.58          | ~ (v1_relat_1 @ X23)
% 6.35/6.58          | ~ (v1_relat_1 @ X22))),
% 6.35/6.58      inference('cnf', [status(esa)], [t55_relat_1])).
% 6.35/6.58  thf('27', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.35/6.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 6.35/6.58          | ~ (v1_relat_1 @ X1)
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.58          | ~ (v1_relat_1 @ X2)
% 6.35/6.58          | ~ (v1_relat_1 @ X1))),
% 6.35/6.58      inference('sup+', [status(thm)], ['25', '26'])).
% 6.35/6.58  thf('28', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('29', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.35/6.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 6.35/6.58          | ~ (v1_relat_1 @ X1)
% 6.35/6.58          | ~ (v1_relat_1 @ X2)
% 6.35/6.58          | ~ (v1_relat_1 @ X1))),
% 6.35/6.58      inference('demod', [status(thm)], ['27', '28'])).
% 6.35/6.58  thf('30', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.58         (~ (v1_relat_1 @ X2)
% 6.35/6.58          | ~ (v1_relat_1 @ X1)
% 6.35/6.58          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.35/6.58              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 6.35/6.58      inference('simplify', [status(thm)], ['29'])).
% 6.35/6.58  thf('31', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 6.35/6.58            (k6_relat_1 @ X0))
% 6.35/6.58            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.35/6.58      inference('sup+', [status(thm)], ['24', '30'])).
% 6.35/6.58  thf('32', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('33', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('34', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 6.35/6.58           (k6_relat_1 @ X0))
% 6.35/6.58           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 6.35/6.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 6.35/6.58  thf('35', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.35/6.58            (k6_relat_1 @ X1))
% 6.35/6.58            = (k5_relat_1 @ 
% 6.35/6.58               (k6_relat_1 @ 
% 6.35/6.58                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 6.35/6.58               (k6_relat_1 @ X1)))
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.35/6.58      inference('sup+', [status(thm)], ['19', '34'])).
% 6.35/6.58  thf('36', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 6.35/6.58           (k6_relat_1 @ X0))
% 6.35/6.58           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 6.35/6.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 6.35/6.58  thf('37', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.58  thf('38', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.58  thf('39', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.58           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.35/6.58              (k6_relat_1 @ X1)))),
% 6.35/6.58      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 6.35/6.58  thf('40', plain,
% 6.35/6.58      (![X0 : $i, X1 : $i]:
% 6.35/6.58         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.58            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 6.35/6.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.35/6.58      inference('sup+', [status(thm)], ['18', '39'])).
% 6.35/6.58  thf('41', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.59  thf('42', plain,
% 6.35/6.59      (![X19 : $i, X20 : $i]:
% 6.35/6.59         (((k7_relat_1 @ X19 @ X20)
% 6.35/6.59            = (k7_relat_1 @ X19 @ (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20)))
% 6.35/6.59          | ~ (v1_relat_1 @ X19))),
% 6.35/6.59      inference('cnf', [status(esa)], [t192_relat_1])).
% 6.35/6.59  thf('43', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['41', '42'])).
% 6.35/6.59  thf('44', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('45', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.59      inference('demod', [status(thm)], ['43', '44'])).
% 6.35/6.59  thf('46', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('47', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('48', plain,
% 6.35/6.59      (![X30 : $i]:
% 6.35/6.59         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X30)) @ X30) = (X30))
% 6.35/6.59          | ~ (v1_relat_1 @ X30))),
% 6.35/6.59      inference('cnf', [status(esa)], [t78_relat_1])).
% 6.35/6.59  thf('49', plain,
% 6.35/6.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X21)
% 6.35/6.59          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 6.35/6.59              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 6.35/6.59          | ~ (v1_relat_1 @ X23)
% 6.35/6.59          | ~ (v1_relat_1 @ X22))),
% 6.35/6.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 6.35/6.59  thf('50', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k5_relat_1 @ X0 @ X1)
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 6.35/6.59               (k5_relat_1 @ X0 @ X1)))
% 6.35/6.59          | ~ (v1_relat_1 @ X0)
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ X0))),
% 6.35/6.59      inference('sup+', [status(thm)], ['48', '49'])).
% 6.35/6.59  thf('51', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('52', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k5_relat_1 @ X0 @ X1)
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 6.35/6.59               (k5_relat_1 @ X0 @ X1)))
% 6.35/6.59          | ~ (v1_relat_1 @ X0)
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['50', '51'])).
% 6.35/6.59  thf('53', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ X0)
% 6.35/6.59          | ((k5_relat_1 @ X0 @ X1)
% 6.35/6.59              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 6.35/6.59                 (k5_relat_1 @ X0 @ X1))))),
% 6.35/6.59      inference('simplify', [status(thm)], ['52'])).
% 6.35/6.59  thf('54', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 6.35/6.59               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['47', '53'])).
% 6.35/6.59  thf('55', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('56', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.59  thf('57', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('58', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('59', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 6.35/6.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 6.35/6.59  thf('60', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59            (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 6.35/6.59            = (k5_relat_1 @ 
% 6.35/6.59               (k6_relat_1 @ 
% 6.35/6.59                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 6.35/6.59               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['17', '59'])).
% 6.35/6.59  thf('61', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.59  thf('62', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.59      inference('demod', [status(thm)], ['43', '44'])).
% 6.35/6.59  thf('63', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 6.35/6.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.35/6.59  thf('64', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('65', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.35/6.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 6.35/6.59  thf('66', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 6.35/6.59           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 6.35/6.59           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.59      inference('sup-', [status(thm)], ['6', '11'])).
% 6.35/6.59  thf('67', plain,
% 6.35/6.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X21)
% 6.35/6.59          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 6.35/6.59              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 6.35/6.59          | ~ (v1_relat_1 @ X23)
% 6.35/6.59          | ~ (v1_relat_1 @ X22))),
% 6.35/6.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 6.35/6.59  thf('68', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59               (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.35/6.59          | ~ (v1_relat_1 @ X2)
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 6.35/6.59      inference('sup+', [status(thm)], ['66', '67'])).
% 6.35/6.59  thf('69', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('70', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('71', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59               (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))
% 6.35/6.59          | ~ (v1_relat_1 @ X2))),
% 6.35/6.59      inference('demod', [status(thm)], ['68', '69', '70'])).
% 6.35/6.59  thf('72', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.35/6.59            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['65', '71'])).
% 6.35/6.59  thf('73', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.35/6.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 6.35/6.59  thf('74', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.59      inference('demod', [status(thm)], ['43', '44'])).
% 6.35/6.59  thf('75', plain,
% 6.35/6.59      (![X32 : $i, X33 : $i]:
% 6.35/6.59         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.59          | ~ (v1_relat_1 @ X33))),
% 6.35/6.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.59  thf(dt_k5_relat_1, axiom,
% 6.35/6.59    (![A:$i,B:$i]:
% 6.35/6.59     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 6.35/6.59       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 6.35/6.59  thf('76', plain,
% 6.35/6.59      (![X16 : $i, X17 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X16)
% 6.35/6.59          | ~ (v1_relat_1 @ X17)
% 6.35/6.59          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 6.35/6.59  thf('77', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['75', '76'])).
% 6.35/6.59  thf('78', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('79', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ X1))),
% 6.35/6.59      inference('demod', [status(thm)], ['77', '78'])).
% 6.35/6.59  thf('80', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.35/6.59      inference('simplify', [status(thm)], ['79'])).
% 6.35/6.59  thf('81', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['74', '80'])).
% 6.35/6.59  thf('82', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('83', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['81', '82'])).
% 6.35/6.59  thf('84', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['72', '73', '83'])).
% 6.35/6.59  thf('85', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['16', '84'])).
% 6.35/6.59  thf('86', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['81', '82'])).
% 6.35/6.59  thf('87', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['85', '86'])).
% 6.35/6.59  thf('88', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 6.35/6.59           (k6_relat_1 @ X0))
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['31', '32', '33'])).
% 6.35/6.59  thf('89', plain,
% 6.35/6.59      (![X16 : $i, X17 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X16)
% 6.35/6.59          | ~ (v1_relat_1 @ X17)
% 6.35/6.59          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 6.35/6.59  thf('90', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['88', '89'])).
% 6.35/6.59  thf('91', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('92', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['81', '82'])).
% 6.35/6.59  thf('93', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['90', '91', '92'])).
% 6.35/6.59  thf('94', plain,
% 6.35/6.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X21)
% 6.35/6.59          | ((k5_relat_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 6.35/6.59              = (k5_relat_1 @ X22 @ (k5_relat_1 @ X21 @ X23)))
% 6.35/6.59          | ~ (v1_relat_1 @ X23)
% 6.35/6.59          | ~ (v1_relat_1 @ X22))),
% 6.35/6.59      inference('cnf', [status(esa)], [t55_relat_1])).
% 6.35/6.59  thf(t76_relat_1, axiom,
% 6.35/6.59    (![A:$i,B:$i]:
% 6.35/6.59     ( ( v1_relat_1 @ B ) =>
% 6.35/6.59       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 6.35/6.59         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 6.35/6.59  thf('95', plain,
% 6.35/6.59      (![X26 : $i, X27 : $i]:
% 6.35/6.59         ((r1_tarski @ (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)) @ X26)
% 6.35/6.59          | ~ (v1_relat_1 @ X26))),
% 6.35/6.59      inference('cnf', [status(esa)], [t76_relat_1])).
% 6.35/6.59  thf('96', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         ((r1_tarski @ 
% 6.35/6.59           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 6.35/6.59           (k5_relat_1 @ X2 @ X1))
% 6.35/6.59          | ~ (v1_relat_1 @ X2)
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['94', '95'])).
% 6.35/6.59  thf('97', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('98', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         ((r1_tarski @ 
% 6.35/6.59           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 6.35/6.59           (k5_relat_1 @ X2 @ X1))
% 6.35/6.59          | ~ (v1_relat_1 @ X2)
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 6.35/6.59      inference('demod', [status(thm)], ['96', '97'])).
% 6.35/6.59  thf('99', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.35/6.59          | (r1_tarski @ 
% 6.35/6.59             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 6.35/6.59             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 6.35/6.59      inference('sup-', [status(thm)], ['93', '98'])).
% 6.35/6.59  thf('100', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('101', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('102', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (r1_tarski @ 
% 6.35/6.59          (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 6.35/6.59           (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 6.35/6.59          (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['99', '100', '101'])).
% 6.35/6.59  thf('103', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('104', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('105', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X2)
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.35/6.59              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 6.35/6.59      inference('simplify', [status(thm)], ['29'])).
% 6.35/6.59  thf('106', plain,
% 6.35/6.59      (![X32 : $i, X33 : $i]:
% 6.35/6.59         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 6.35/6.59          | ~ (v1_relat_1 @ X33))),
% 6.35/6.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 6.35/6.59  thf('107', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 6.35/6.59            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ X2)
% 6.35/6.59          | ~ (v1_relat_1 @ X0)
% 6.35/6.59          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['105', '106'])).
% 6.35/6.59  thf('108', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.59          | ((k7_relat_1 @ 
% 6.35/6.59              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ X2)
% 6.35/6.59              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.35/6.59                 (k6_relat_1 @ X1))))),
% 6.35/6.59      inference('sup-', [status(thm)], ['104', '107'])).
% 6.35/6.59  thf('109', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['81', '82'])).
% 6.35/6.59  thf('110', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('111', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('112', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('113', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('114', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (~ (v1_relat_1 @ X2)
% 6.35/6.59          | ~ (v1_relat_1 @ X1)
% 6.35/6.59          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 6.35/6.59              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 6.35/6.59      inference('simplify', [status(thm)], ['29'])).
% 6.35/6.59  thf('115', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.35/6.59            (k6_relat_1 @ X1))
% 6.35/6.59            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.35/6.59               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.35/6.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['113', '114'])).
% 6.35/6.59  thf('116', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('117', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 6.35/6.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 6.35/6.59  thf('118', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.35/6.59           (k6_relat_1 @ X1))
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.35/6.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)], ['115', '116', '117'])).
% 6.35/6.59  thf('119', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 6.35/6.59           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 6.35/6.59              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 6.35/6.59      inference('demod', [status(thm)],
% 6.35/6.59                ['108', '109', '110', '111', '112', '118'])).
% 6.35/6.59  thf('120', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 6.35/6.59      inference('demod', [status(thm)], ['40', '45', '46'])).
% 6.35/6.59  thf('121', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.35/6.59         (r1_tarski @ 
% 6.35/6.59          (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X0) @ X1) @ 
% 6.35/6.59          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.35/6.59      inference('demod', [status(thm)], ['102', '103', '119', '120'])).
% 6.35/6.59  thf('122', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.35/6.59          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.35/6.59      inference('sup+', [status(thm)], ['87', '121'])).
% 6.35/6.59  thf(d10_xboole_0, axiom,
% 6.35/6.59    (![A:$i,B:$i]:
% 6.35/6.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.35/6.59  thf('123', plain,
% 6.35/6.59      (![X0 : $i, X2 : $i]:
% 6.35/6.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.35/6.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.35/6.59  thf('124', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.35/6.59             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.35/6.59          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 6.35/6.59      inference('sup-', [status(thm)], ['122', '123'])).
% 6.35/6.59  thf('125', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 6.35/6.59          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.35/6.59      inference('sup+', [status(thm)], ['87', '121'])).
% 6.35/6.59  thf('126', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 6.35/6.59      inference('demod', [status(thm)], ['124', '125'])).
% 6.35/6.59  thf('127', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 6.35/6.59           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.59      inference('demod', [status(thm)], ['15', '126'])).
% 6.35/6.59  thf('128', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 6.35/6.59           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 6.35/6.59      inference('demod', [status(thm)], ['43', '44'])).
% 6.35/6.59  thf('129', plain,
% 6.35/6.59      (![X0 : $i, X1 : $i]:
% 6.35/6.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 6.35/6.59           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.35/6.59      inference('sup+', [status(thm)], ['127', '128'])).
% 6.35/6.59  thf('130', plain,
% 6.35/6.59      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.35/6.59         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 6.35/6.59      inference('demod', [status(thm)], ['4', '129'])).
% 6.35/6.59  thf('131', plain, ($false), inference('simplify', [status(thm)], ['130'])).
% 6.35/6.59  
% 6.35/6.59  % SZS output end Refutation
% 6.35/6.59  
% 6.35/6.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
