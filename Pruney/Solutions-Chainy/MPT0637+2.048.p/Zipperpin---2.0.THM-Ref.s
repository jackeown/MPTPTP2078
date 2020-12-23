%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.COxYYLwzkP

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:02 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  136 (1489 expanded)
%              Number of leaves         :   26 ( 543 expanded)
%              Depth                    :   16
%              Number of atoms          : 1153 (13278 expanded)
%              Number of equality atoms :   84 ( 966 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X32 ) ) @ X32 )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('30',plain,(
    ! [X33: $i] :
      ( ( ( k5_relat_1 @ X33 @ ( k6_relat_1 @ ( k2_relat_1 @ X33 ) ) )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('55',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X18 @ X17 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('67',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('74',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X30 )
        = X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','78'])).

thf('80',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k8_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','50','51','52','53','54','59','60','81','82','89'])).

thf('91',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','50','51','52','53','54','59','60','81','82','89'])).

thf('93',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('96',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['94','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','50','51','52','53','54','59','60','81','82','89'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','50','51','52','53','54','59','60','81','82','89'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','106'])).

thf('108',plain,(
    $false ),
    inference(simplify,[status(thm)],['107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.COxYYLwzkP
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.65/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.84  % Solved by: fo/fo7.sh
% 0.65/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.84  % done 347 iterations in 0.354s
% 0.65/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.84  % SZS output start Refutation
% 0.65/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.65/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.65/0.84  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.65/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.65/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.65/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.84  thf(t123_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.65/0.84  thf('0', plain,
% 0.65/0.84      (![X19 : $i, X20 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 0.65/0.84          | ~ (v1_relat_1 @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.65/0.84  thf(t43_funct_1, conjecture,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.65/0.84       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.84    (~( ![A:$i,B:$i]:
% 0.65/0.84        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.65/0.84          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.65/0.84    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.65/0.84  thf('1', plain,
% 0.65/0.84      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.65/0.84         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('2', plain,
% 0.65/0.84      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.65/0.84          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.65/0.84        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['0', '1'])).
% 0.65/0.84  thf(fc3_funct_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.65/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.65/0.84  thf('3', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('4', plain,
% 0.65/0.84      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.65/0.84         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.84  thf(t71_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.65/0.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.65/0.84  thf('5', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.65/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.65/0.84  thf(t78_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ A ) =>
% 0.65/0.84       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.65/0.84  thf('6', plain,
% 0.65/0.84      (![X32 : $i]:
% 0.65/0.84         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X32)) @ X32) = (X32))
% 0.65/0.84          | ~ (v1_relat_1 @ X32))),
% 0.65/0.84      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.65/0.84  thf('7', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.65/0.84            = (k6_relat_1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['5', '6'])).
% 0.65/0.84  thf('8', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('9', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.65/0.84  thf('10', plain,
% 0.65/0.84      (![X19 : $i, X20 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 0.65/0.84          | ~ (v1_relat_1 @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.65/0.84  thf(t55_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ A ) =>
% 0.65/0.84       ( ![B:$i]:
% 0.65/0.84         ( ( v1_relat_1 @ B ) =>
% 0.65/0.84           ( ![C:$i]:
% 0.65/0.84             ( ( v1_relat_1 @ C ) =>
% 0.65/0.84               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.65/0.84                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.65/0.84  thf('11', plain,
% 0.65/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X23)
% 0.65/0.84          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.65/0.84              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 0.65/0.84          | ~ (v1_relat_1 @ X25)
% 0.65/0.84          | ~ (v1_relat_1 @ X24))),
% 0.65/0.84      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.65/0.84  thf('12', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.65/0.84            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.65/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.65/0.84  thf('13', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('14', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.65/0.84            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.65/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['12', '13'])).
% 0.65/0.84  thf('15', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ((k8_relat_1 @ X1 @ 
% 0.65/0.84              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)))
% 0.65/0.84              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84                 (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['9', '14'])).
% 0.65/0.84  thf('16', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('17', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('18', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('19', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.65/0.84  thf('20', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 0.65/0.84      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.65/0.84  thf('21', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.65/0.84  thf('22', plain,
% 0.65/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X23)
% 0.65/0.84          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.65/0.84              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 0.65/0.84          | ~ (v1_relat_1 @ X25)
% 0.65/0.84          | ~ (v1_relat_1 @ X24))),
% 0.65/0.84      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.65/0.84  thf('23', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.65/0.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['21', '22'])).
% 0.65/0.84  thf('24', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('25', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('26', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.65/0.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.65/0.84          | ~ (v1_relat_1 @ X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.65/0.84  thf('27', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['20', '26'])).
% 0.65/0.84  thf('28', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('29', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.84  thf(t80_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ A ) =>
% 0.65/0.84       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.65/0.84  thf('30', plain,
% 0.65/0.84      (![X33 : $i]:
% 0.65/0.84         (((k5_relat_1 @ X33 @ (k6_relat_1 @ (k2_relat_1 @ X33))) = (X33))
% 0.65/0.84          | ~ (v1_relat_1 @ X33))),
% 0.65/0.84      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.65/0.84  thf('31', plain,
% 0.65/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X23)
% 0.65/0.84          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.65/0.84              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 0.65/0.84          | ~ (v1_relat_1 @ X25)
% 0.65/0.84          | ~ (v1_relat_1 @ X24))),
% 0.65/0.84      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.65/0.84  thf('32', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k5_relat_1 @ X1 @ X0)
% 0.65/0.84            = (k5_relat_1 @ X1 @ 
% 0.65/0.84               (k5_relat_1 @ X0 @ 
% 0.65/0.84                (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 0.65/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ 
% 0.65/0.84               (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('sup+', [status(thm)], ['30', '31'])).
% 0.65/0.84  thf('33', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('34', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k5_relat_1 @ X1 @ X0)
% 0.65/0.84            = (k5_relat_1 @ X1 @ 
% 0.65/0.84               (k5_relat_1 @ X0 @ 
% 0.65/0.84                (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 0.65/0.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['32', '33'])).
% 0.65/0.84  thf('35', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84                 (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.65/0.84                  (k6_relat_1 @ 
% 0.65/0.84                   (k2_relat_1 @ 
% 0.65/0.84                    (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['29', '34'])).
% 0.65/0.84  thf('36', plain,
% 0.65/0.84      (![X19 : $i, X20 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 0.65/0.84          | ~ (v1_relat_1 @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.65/0.84  thf(t94_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.65/0.84  thf('37', plain,
% 0.65/0.84      (![X36 : $i, X37 : $i]:
% 0.65/0.84         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.65/0.84          | ~ (v1_relat_1 @ X37))),
% 0.65/0.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.65/0.84  thf('38', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.65/0.84            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['36', '37'])).
% 0.65/0.84  thf('39', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('40', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('41', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.65/0.84  thf('42', plain,
% 0.65/0.84      (![X36 : $i, X37 : $i]:
% 0.65/0.84         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.65/0.84          | ~ (v1_relat_1 @ X37))),
% 0.65/0.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.65/0.84  thf(dt_k5_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.65/0.84       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.65/0.84  thf('43', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X12)
% 0.65/0.84          | ~ (v1_relat_1 @ X13)
% 0.65/0.84          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.65/0.84      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.65/0.84  thf('44', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['42', '43'])).
% 0.65/0.84  thf('45', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('46', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.65/0.84          | ~ (v1_relat_1 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['44', '45'])).
% 0.65/0.84  thf('47', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.65/0.84      inference('simplify', [status(thm)], ['46'])).
% 0.65/0.84  thf('48', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['41', '47'])).
% 0.65/0.84  thf('49', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('50', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['48', '49'])).
% 0.65/0.84  thf('51', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('52', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('53', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.84  thf('54', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.84  thf('55', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.65/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.65/0.84  thf(t119_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.65/0.84         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.65/0.84  thf('56', plain,
% 0.65/0.84      (![X17 : $i, X18 : $i]:
% 0.65/0.84         (((k2_relat_1 @ (k8_relat_1 @ X18 @ X17))
% 0.65/0.84            = (k3_xboole_0 @ (k2_relat_1 @ X17) @ X18))
% 0.65/0.84          | ~ (v1_relat_1 @ X17))),
% 0.65/0.84      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.65/0.84  thf('57', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84            = (k3_xboole_0 @ X0 @ X1))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['55', '56'])).
% 0.65/0.84  thf('58', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('59', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84           = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['57', '58'])).
% 0.65/0.84  thf('60', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.84  thf('61', plain,
% 0.65/0.84      (![X19 : $i, X20 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 0.65/0.84          | ~ (v1_relat_1 @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.65/0.84  thf('62', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84           = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['57', '58'])).
% 0.65/0.84  thf('63', plain,
% 0.65/0.84      (![X19 : $i, X20 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 0.65/0.84          | ~ (v1_relat_1 @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.65/0.84  thf(t45_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ A ) =>
% 0.65/0.84       ( ![B:$i]:
% 0.65/0.84         ( ( v1_relat_1 @ B ) =>
% 0.65/0.84           ( r1_tarski @
% 0.65/0.84             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.65/0.84  thf('64', plain,
% 0.65/0.84      (![X21 : $i, X22 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X21)
% 0.65/0.84          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 0.65/0.84             (k2_relat_1 @ X21))
% 0.65/0.84          | ~ (v1_relat_1 @ X22))),
% 0.65/0.84      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.65/0.84  thf('65', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.65/0.84           (k2_relat_1 @ (k6_relat_1 @ X1)))
% 0.65/0.84          | ~ (v1_relat_1 @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['63', '64'])).
% 0.65/0.84  thf('66', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.65/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.65/0.84  thf('67', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('68', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ X0))),
% 0.65/0.84      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.65/0.84  thf('69', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (v1_relat_1 @ X0)
% 0.65/0.84          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1))),
% 0.65/0.84      inference('simplify', [status(thm)], ['68'])).
% 0.65/0.84  thf('70', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['62', '69'])).
% 0.65/0.84  thf('71', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('72', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.65/0.84      inference('demod', [status(thm)], ['70', '71'])).
% 0.65/0.84  thf('73', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.65/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.65/0.84  thf(t77_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.65/0.84         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.65/0.84  thf('74', plain,
% 0.65/0.84      (![X30 : $i, X31 : $i]:
% 0.65/0.84         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.65/0.84          | ((k5_relat_1 @ (k6_relat_1 @ X31) @ X30) = (X30))
% 0.65/0.84          | ~ (v1_relat_1 @ X30))),
% 0.65/0.84      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.65/0.84  thf('75', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.65/0.84          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.65/0.84              = (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['73', '74'])).
% 0.65/0.84  thf('76', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('77', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.65/0.84          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.65/0.84              = (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['75', '76'])).
% 0.65/0.84  thf('78', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['72', '77'])).
% 0.65/0.84  thf('79', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 0.65/0.84            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['61', '78'])).
% 0.65/0.84  thf('80', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('81', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['79', '80'])).
% 0.65/0.84  thf('82', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.84  thf('83', plain,
% 0.65/0.84      (![X19 : $i, X20 : $i]:
% 0.65/0.84         (((k8_relat_1 @ X20 @ X19) = (k5_relat_1 @ X19 @ (k6_relat_1 @ X20)))
% 0.65/0.84          | ~ (v1_relat_1 @ X19))),
% 0.65/0.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.65/0.84  thf(t17_xboole_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.65/0.84  thf('84', plain,
% 0.65/0.84      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.65/0.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.65/0.84  thf('85', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.65/0.84          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.65/0.84              = (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['75', '76'])).
% 0.65/0.84  thf('86', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.65/0.84           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['84', '85'])).
% 0.65/0.84  thf('87', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.65/0.84            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['83', '86'])).
% 0.65/0.84  thf('88', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('89', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('demod', [status(thm)], ['87', '88'])).
% 0.65/0.84  thf('90', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['35', '50', '51', '52', '53', '54', '59', '60', '81', '82', 
% 0.65/0.84                 '89'])).
% 0.65/0.84  thf('91', plain,
% 0.65/0.84      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.65/0.84         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.65/0.84      inference('demod', [status(thm)], ['4', '90'])).
% 0.65/0.84  thf('92', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['35', '50', '51', '52', '53', '54', '59', '60', '81', '82', 
% 0.65/0.84                 '89'])).
% 0.65/0.84  thf('93', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.65/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.65/0.84  thf('94', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.65/0.84           = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('sup+', [status(thm)], ['92', '93'])).
% 0.65/0.84  thf('95', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.65/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.65/0.84  thf(t90_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ B ) =>
% 0.65/0.84       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.65/0.84         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.65/0.84  thf('96', plain,
% 0.65/0.84      (![X34 : $i, X35 : $i]:
% 0.65/0.84         (((k1_relat_1 @ (k7_relat_1 @ X34 @ X35))
% 0.65/0.84            = (k3_xboole_0 @ (k1_relat_1 @ X34) @ X35))
% 0.65/0.84          | ~ (v1_relat_1 @ X34))),
% 0.65/0.84      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.65/0.84  thf('97', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.65/0.84            = (k3_xboole_0 @ X0 @ X1))
% 0.65/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['95', '96'])).
% 0.65/0.84  thf('98', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.65/0.84  thf('99', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.65/0.84           = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['97', '98'])).
% 0.65/0.84  thf('100', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.65/0.84  thf('101', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.65/0.84           = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('demod', [status(thm)], ['99', '100'])).
% 0.65/0.84  thf('102', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.84      inference('sup+', [status(thm)], ['94', '101'])).
% 0.65/0.84  thf('103', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['35', '50', '51', '52', '53', '54', '59', '60', '81', '82', 
% 0.65/0.84                 '89'])).
% 0.65/0.84  thf('104', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['102', '103'])).
% 0.65/0.84  thf('105', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.65/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.84      inference('demod', [status(thm)],
% 0.65/0.84                ['35', '50', '51', '52', '53', '54', '59', '60', '81', '82', 
% 0.65/0.84                 '89'])).
% 0.65/0.84  thf('106', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i]:
% 0.65/0.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.65/0.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['104', '105'])).
% 0.65/0.84  thf('107', plain,
% 0.65/0.84      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.65/0.84         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.65/0.84      inference('demod', [status(thm)], ['91', '106'])).
% 0.65/0.84  thf('108', plain, ($false), inference('simplify', [status(thm)], ['107'])).
% 0.65/0.84  
% 0.65/0.84  % SZS output end Refutation
% 0.65/0.84  
% 0.65/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
