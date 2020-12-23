%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jVihmfutOB

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:06 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  286 (4800 expanded)
%              Number of leaves         :   30 (1721 expanded)
%              Depth                    :   33
%              Number of atoms          : 2793 (45230 expanded)
%              Number of equality atoms :  197 (2791 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

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
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('15',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf('22',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X24 ) @ ( k4_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('30',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('31',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('33',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('34',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k5_relat_1 @ X27 @ ( k5_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('41',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('45',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k8_relat_1 @ X19 @ ( k7_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('64',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('65',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('71',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X33 @ X34 ) @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X23 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('78',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k8_relat_1 @ X18 @ X17 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('91',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k5_relat_1 @ X27 @ ( k5_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('97',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('98',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('101',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) @ X21 )
        = ( k8_relat_1 @ X19 @ ( k7_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('106',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('109',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','111','112'])).

thf('114',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X24 ) @ ( k4_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['88','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['87','127'])).

thf('129',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['128','133'])).

thf('135',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('136',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('137',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('146',plain,(
    ! [X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ ( k1_relat_1 @ X37 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X33 @ X34 ) @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k8_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('167',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('170',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('171',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['165','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['164','173'])).

thf('175',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('181',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['180','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['178','179','192'])).

thf('194',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['136','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','199'])).

thf('201',plain,(
    ! [X32: $i] :
      ( ( ( k5_relat_1 @ X32 @ ( k6_relat_1 @ ( k2_relat_1 @ X32 ) ) )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('202',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('212',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212'])).

thf('214',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('217',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['200','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['134','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','63','64','65'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('242',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('244',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('247',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','52','62'])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['242','243','244','245','246','247','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['223','224','225','249','250','251'])).

thf('253',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','252'])).

thf('254',plain,(
    $false ),
    inference(simplify,[status(thm)],['253'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jVihmfutOB
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:24:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.65/2.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.65/2.83  % Solved by: fo/fo7.sh
% 2.65/2.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.83  % done 2326 iterations in 2.389s
% 2.65/2.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.65/2.83  % SZS output start Refutation
% 2.65/2.83  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.65/2.83  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.65/2.83  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 2.65/2.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.65/2.83  thf(sk_B_type, type, sk_B: $i).
% 2.65/2.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.65/2.83  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.65/2.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.65/2.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.65/2.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.65/2.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.65/2.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.65/2.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.65/2.83  thf(t123_relat_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ B ) =>
% 2.65/2.83       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 2.65/2.83  thf('0', plain,
% 2.65/2.83      (![X15 : $i, X16 : $i]:
% 2.65/2.83         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.83          | ~ (v1_relat_1 @ X15))),
% 2.65/2.83      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.83  thf(t43_funct_1, conjecture,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.65/2.83       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.65/2.83  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.83    (~( ![A:$i,B:$i]:
% 2.65/2.83        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.65/2.83          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.65/2.83    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.65/2.83  thf('1', plain,
% 2.65/2.83      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.65/2.83         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('2', plain,
% 2.65/2.83      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 2.65/2.83          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.65/2.83        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 2.65/2.83      inference('sup-', [status(thm)], ['0', '1'])).
% 2.65/2.83  thf(fc24_relat_1, axiom,
% 2.65/2.83    (![A:$i]:
% 2.65/2.83     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 2.65/2.83       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 2.65/2.83       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.65/2.83  thf('3', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.83      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.83  thf('4', plain,
% 2.65/2.83      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 2.65/2.83         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.65/2.83      inference('demod', [status(thm)], ['2', '3'])).
% 2.65/2.83  thf(t71_relat_1, axiom,
% 2.65/2.83    (![A:$i]:
% 2.65/2.83     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.65/2.83       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.65/2.83  thf('5', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 2.65/2.83      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.83  thf(t98_relat_1, axiom,
% 2.65/2.83    (![A:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ A ) =>
% 2.65/2.83       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 2.65/2.83  thf('6', plain,
% 2.65/2.83      (![X37 : $i]:
% 2.65/2.83         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 2.65/2.83          | ~ (v1_relat_1 @ X37))),
% 2.65/2.83      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.65/2.83  thf('7', plain,
% 2.65/2.83      (![X0 : $i]:
% 2.65/2.83         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 2.65/2.83          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.83      inference('sup+', [status(thm)], ['5', '6'])).
% 2.65/2.83  thf('8', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.83      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.83  thf('9', plain,
% 2.65/2.83      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 2.65/2.83      inference('demod', [status(thm)], ['7', '8'])).
% 2.65/2.83  thf(t100_relat_1, axiom,
% 2.65/2.83    (![A:$i,B:$i,C:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ C ) =>
% 2.65/2.83       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.65/2.83         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 2.65/2.83  thf('10', plain,
% 2.65/2.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.65/2.83         (((k7_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 2.65/2.83            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ X10 @ X11)))
% 2.65/2.83          | ~ (v1_relat_1 @ X9))),
% 2.65/2.83      inference('cnf', [status(esa)], [t100_relat_1])).
% 2.65/2.83  thf('11', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.83            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 2.65/2.83          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.83      inference('sup+', [status(thm)], ['9', '10'])).
% 2.65/2.83  thf('12', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.83      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.83  thf('13', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.83           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 2.65/2.83      inference('demod', [status(thm)], ['11', '12'])).
% 2.65/2.83  thf('14', plain,
% 2.65/2.83      (![X15 : $i, X16 : $i]:
% 2.65/2.83         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.83          | ~ (v1_relat_1 @ X15))),
% 2.65/2.83      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.83  thf(t94_relat_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ B ) =>
% 2.65/2.83       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.65/2.83  thf('15', plain,
% 2.65/2.83      (![X35 : $i, X36 : $i]:
% 2.65/2.83         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.83          | ~ (v1_relat_1 @ X36))),
% 2.65/2.83      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.83  thf('16', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.83            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.83          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.65/2.83          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.65/2.83      inference('sup+', [status(thm)], ['14', '15'])).
% 2.65/2.83  thf('17', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.83      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.83  thf('18', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.83      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.83  thf('19', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.83           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.83      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.83  thf('20', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.83           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.83      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.83  thf('21', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.83           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 2.65/2.83      inference('demod', [status(thm)], ['13', '19', '20'])).
% 2.65/2.83  thf('22', plain,
% 2.65/2.83      (![X35 : $i, X36 : $i]:
% 2.65/2.83         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.83          | ~ (v1_relat_1 @ X36))),
% 2.65/2.83      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.83  thf(t72_relat_1, axiom,
% 2.65/2.83    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 2.65/2.83  thf('23', plain,
% 2.65/2.83      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 2.65/2.83      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.65/2.83  thf(t54_relat_1, axiom,
% 2.65/2.83    (![A:$i]:
% 2.65/2.83     ( ( v1_relat_1 @ A ) =>
% 2.65/2.83       ( ![B:$i]:
% 2.65/2.83         ( ( v1_relat_1 @ B ) =>
% 2.65/2.83           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.65/2.83             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 2.65/2.83  thf('24', plain,
% 2.65/2.83      (![X24 : $i, X25 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X24)
% 2.65/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X25 @ X24))
% 2.65/2.84              = (k5_relat_1 @ (k4_relat_1 @ X24) @ (k4_relat_1 @ X25)))
% 2.65/2.84          | ~ (v1_relat_1 @ X25))),
% 2.65/2.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.65/2.84  thf('25', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['23', '24'])).
% 2.65/2.84  thf('26', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('27', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['25', '26'])).
% 2.65/2.84  thf('28', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.65/2.84               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['22', '27'])).
% 2.65/2.84  thf('29', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.84  thf('30', plain,
% 2.65/2.84      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 2.65/2.84      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.65/2.84  thf('31', plain,
% 2.65/2.84      (![X35 : $i, X36 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.84          | ~ (v1_relat_1 @ X36))),
% 2.65/2.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.84  thf('32', plain,
% 2.65/2.84      (![X15 : $i, X16 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.84          | ~ (v1_relat_1 @ X15))),
% 2.65/2.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.84  thf('33', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf(t80_relat_1, axiom,
% 2.65/2.84    (![A:$i]:
% 2.65/2.84     ( ( v1_relat_1 @ A ) =>
% 2.65/2.84       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.65/2.84  thf('34', plain,
% 2.65/2.84      (![X32 : $i]:
% 2.65/2.84         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 2.65/2.84          | ~ (v1_relat_1 @ X32))),
% 2.65/2.84      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.65/2.84  thf('35', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.65/2.84            = (k6_relat_1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['33', '34'])).
% 2.65/2.84  thf('36', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('37', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k6_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['35', '36'])).
% 2.65/2.84  thf(t55_relat_1, axiom,
% 2.65/2.84    (![A:$i]:
% 2.65/2.84     ( ( v1_relat_1 @ A ) =>
% 2.65/2.84       ( ![B:$i]:
% 2.65/2.84         ( ( v1_relat_1 @ B ) =>
% 2.65/2.84           ( ![C:$i]:
% 2.65/2.84             ( ( v1_relat_1 @ C ) =>
% 2.65/2.84               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.65/2.84                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.65/2.84  thf('38', plain,
% 2.65/2.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X26)
% 2.65/2.84          | ((k5_relat_1 @ (k5_relat_1 @ X27 @ X26) @ X28)
% 2.65/2.84              = (k5_relat_1 @ X27 @ (k5_relat_1 @ X26 @ X28)))
% 2.65/2.84          | ~ (v1_relat_1 @ X28)
% 2.65/2.84          | ~ (v1_relat_1 @ X27))),
% 2.65/2.84      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.65/2.84  thf('39', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['37', '38'])).
% 2.65/2.84  thf('40', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('41', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('42', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.65/2.84  thf('43', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['32', '42'])).
% 2.65/2.84  thf('44', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('45', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('46', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.65/2.84  thf('47', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84            = (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['31', '46'])).
% 2.65/2.84  thf('48', plain,
% 2.65/2.84      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['7', '8'])).
% 2.65/2.84  thf(t140_relat_1, axiom,
% 2.65/2.84    (![A:$i,B:$i,C:$i]:
% 2.65/2.84     ( ( v1_relat_1 @ C ) =>
% 2.65/2.84       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 2.65/2.84         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 2.65/2.84  thf('49', plain,
% 2.65/2.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k8_relat_1 @ X19 @ X20) @ X21)
% 2.65/2.84            = (k8_relat_1 @ X19 @ (k7_relat_1 @ X20 @ X21)))
% 2.65/2.84          | ~ (v1_relat_1 @ X20))),
% 2.65/2.84      inference('cnf', [status(esa)], [t140_relat_1])).
% 2.65/2.84  thf('50', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 2.65/2.84            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['48', '49'])).
% 2.65/2.84  thf('51', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('52', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['50', '51'])).
% 2.65/2.84  thf('53', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.84  thf('54', plain,
% 2.65/2.84      (![X35 : $i, X36 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.84          | ~ (v1_relat_1 @ X36))),
% 2.65/2.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.84  thf(dt_k5_relat_1, axiom,
% 2.65/2.84    (![A:$i,B:$i]:
% 2.65/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.65/2.84       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.65/2.84  thf('55', plain,
% 2.65/2.84      (![X7 : $i, X8 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X7)
% 2.65/2.84          | ~ (v1_relat_1 @ X8)
% 2.65/2.84          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 2.65/2.84      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.65/2.84  thf('56', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['54', '55'])).
% 2.65/2.84  thf('57', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('58', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['56', '57'])).
% 2.65/2.84  thf('59', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.84      inference('simplify', [status(thm)], ['58'])).
% 2.65/2.84  thf('60', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['53', '59'])).
% 2.65/2.84  thf('61', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('62', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('63', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('64', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('65', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('66', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('67', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['21', '66'])).
% 2.65/2.84  thf('68', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('69', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['67', '68'])).
% 2.65/2.84  thf('70', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.84  thf(t88_relat_1, axiom,
% 2.65/2.84    (![A:$i,B:$i]:
% 2.65/2.84     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 2.65/2.84  thf('71', plain,
% 2.65/2.84      (![X33 : $i, X34 : $i]:
% 2.65/2.84         ((r1_tarski @ (k7_relat_1 @ X33 @ X34) @ X33) | ~ (v1_relat_1 @ X33))),
% 2.65/2.84      inference('cnf', [status(esa)], [t88_relat_1])).
% 2.65/2.84  thf('72', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 2.65/2.84           (k6_relat_1 @ X1))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['70', '71'])).
% 2.65/2.84  thf('73', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('74', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['72', '73'])).
% 2.65/2.84  thf(t25_relat_1, axiom,
% 2.65/2.84    (![A:$i]:
% 2.65/2.84     ( ( v1_relat_1 @ A ) =>
% 2.65/2.84       ( ![B:$i]:
% 2.65/2.84         ( ( v1_relat_1 @ B ) =>
% 2.65/2.84           ( ( r1_tarski @ A @ B ) =>
% 2.65/2.84             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 2.65/2.84               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 2.65/2.84  thf('75', plain,
% 2.65/2.84      (![X22 : $i, X23 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X22)
% 2.65/2.84          | (r1_tarski @ (k1_relat_1 @ X23) @ (k1_relat_1 @ X22))
% 2.65/2.84          | ~ (r1_tarski @ X23 @ X22)
% 2.65/2.84          | ~ (v1_relat_1 @ X23))),
% 2.65/2.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.65/2.84  thf('76', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.65/2.84          | (r1_tarski @ 
% 2.65/2.84             (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 2.65/2.84             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup-', [status(thm)], ['74', '75'])).
% 2.65/2.84  thf('77', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('78', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('79', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('80', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ X0)),
% 2.65/2.84      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 2.65/2.84  thf('81', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 2.65/2.84          (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.84      inference('sup+', [status(thm)], ['69', '80'])).
% 2.65/2.84  thf('82', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf(t125_relat_1, axiom,
% 2.65/2.84    (![A:$i,B:$i]:
% 2.65/2.84     ( ( v1_relat_1 @ B ) =>
% 2.65/2.84       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.65/2.84         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 2.65/2.84  thf('83', plain,
% 2.65/2.84      (![X17 : $i, X18 : $i]:
% 2.65/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 2.65/2.84          | ((k8_relat_1 @ X18 @ X17) = (X17))
% 2.65/2.84          | ~ (v1_relat_1 @ X17))),
% 2.65/2.84      inference('cnf', [status(esa)], [t125_relat_1])).
% 2.65/2.84  thf('84', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (r1_tarski @ X0 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.65/2.84          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup-', [status(thm)], ['82', '83'])).
% 2.65/2.84  thf('85', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('86', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (r1_tarski @ X0 @ X1)
% 2.65/2.84          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['84', '85'])).
% 2.65/2.84  thf('87', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 2.65/2.84           (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))))
% 2.65/2.84           = (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 2.65/2.84      inference('sup-', [status(thm)], ['81', '86'])).
% 2.65/2.84  thf('88', plain,
% 2.65/2.84      (![X15 : $i, X16 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.84          | ~ (v1_relat_1 @ X15))),
% 2.65/2.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.84  thf('89', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('90', plain,
% 2.65/2.84      (![X15 : $i, X16 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.84          | ~ (v1_relat_1 @ X15))),
% 2.65/2.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.84  thf('91', plain,
% 2.65/2.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X26)
% 2.65/2.84          | ((k5_relat_1 @ (k5_relat_1 @ X27 @ X26) @ X28)
% 2.65/2.84              = (k5_relat_1 @ X27 @ (k5_relat_1 @ X26 @ X28)))
% 2.65/2.84          | ~ (v1_relat_1 @ X28)
% 2.65/2.84          | ~ (v1_relat_1 @ X27))),
% 2.65/2.84      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.65/2.84  thf('92', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 2.65/2.84            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['90', '91'])).
% 2.65/2.84  thf('93', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('94', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 2.65/2.84            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['92', '93'])).
% 2.65/2.84  thf('95', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.65/2.84          | ((k8_relat_1 @ X2 @ 
% 2.65/2.84              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 2.65/2.84              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 2.65/2.84      inference('sup-', [status(thm)], ['89', '94'])).
% 2.65/2.84  thf('96', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('97', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('98', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('99', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('100', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.84  thf('101', plain,
% 2.65/2.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k8_relat_1 @ X19 @ X20) @ X21)
% 2.65/2.84            = (k8_relat_1 @ X19 @ (k7_relat_1 @ X20 @ X21)))
% 2.65/2.84          | ~ (v1_relat_1 @ X20))),
% 2.65/2.84      inference('cnf', [status(esa)], [t140_relat_1])).
% 2.65/2.84  thf('102', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 2.65/2.84            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['100', '101'])).
% 2.65/2.84  thf('103', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('104', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['102', '103'])).
% 2.65/2.84  thf('105', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.84  thf('106', plain,
% 2.65/2.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 2.65/2.84            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ X10 @ X11)))
% 2.65/2.84          | ~ (v1_relat_1 @ X9))),
% 2.65/2.84      inference('cnf', [status(esa)], [t100_relat_1])).
% 2.65/2.84  thf('107', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 2.65/2.84            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['105', '106'])).
% 2.65/2.84  thf('108', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.65/2.84  thf('109', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('110', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 2.65/2.84      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.65/2.84  thf('111', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['104', '110'])).
% 2.65/2.84  thf('112', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('113', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.65/2.84           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 2.65/2.84      inference('demod', [status(thm)],
% 2.65/2.84                ['95', '96', '97', '98', '99', '111', '112'])).
% 2.65/2.84  thf('114', plain,
% 2.65/2.84      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 2.65/2.84      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.65/2.84  thf('115', plain,
% 2.65/2.84      (![X24 : $i, X25 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X24)
% 2.65/2.84          | ((k4_relat_1 @ (k5_relat_1 @ X25 @ X24))
% 2.65/2.84              = (k5_relat_1 @ (k4_relat_1 @ X24) @ (k4_relat_1 @ X25)))
% 2.65/2.84          | ~ (v1_relat_1 @ X25))),
% 2.65/2.84      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.65/2.84  thf('116', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.65/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('sup+', [status(thm)], ['114', '115'])).
% 2.65/2.84  thf('117', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('118', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.65/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['116', '117'])).
% 2.65/2.84  thf('119', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k4_relat_1 @ 
% 2.65/2.84            (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 2.65/2.84            = (k5_relat_1 @ 
% 2.65/2.84               (k4_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))) @ 
% 2.65/2.84               (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['113', '118'])).
% 2.65/2.84  thf('120', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('121', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('122', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('123', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 2.65/2.84           = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ 
% 2.65/2.84              (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 2.65/2.84  thf('124', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k8_relat_1 @ (k3_xboole_0 @ X1 @ X2) @ (k6_relat_1 @ X0))
% 2.65/2.84            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['88', '123'])).
% 2.65/2.84  thf('125', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['104', '110'])).
% 2.65/2.84  thf('126', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('127', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X2) @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['124', '125', '126'])).
% 2.65/2.84  thf('128', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ 
% 2.65/2.84           (k6_relat_1 @ 
% 2.65/2.84            (k3_xboole_0 @ X1 @ 
% 2.65/2.84             (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))))
% 2.65/2.84           = (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))))),
% 2.65/2.84      inference('demod', [status(thm)], ['87', '127'])).
% 2.65/2.84  thf('129', plain,
% 2.65/2.84      (![X37 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 2.65/2.84          | ~ (v1_relat_1 @ X37))),
% 2.65/2.84      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.65/2.84  thf('130', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 2.65/2.84      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.65/2.84  thf('131', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 2.65/2.84            = (k8_relat_1 @ X1 @ 
% 2.65/2.84               (k6_relat_1 @ 
% 2.65/2.84                (k3_xboole_0 @ X0 @ 
% 2.65/2.84                 (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['129', '130'])).
% 2.65/2.84  thf('132', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('133', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k8_relat_1 @ X1 @ 
% 2.65/2.84              (k6_relat_1 @ 
% 2.65/2.84               (k3_xboole_0 @ X0 @ 
% 2.65/2.84                (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))))),
% 2.65/2.84      inference('demod', [status(thm)], ['131', '132'])).
% 2.65/2.84  thf('134', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['128', '133'])).
% 2.65/2.84  thf('135', plain,
% 2.65/2.84      (![X37 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 2.65/2.84          | ~ (v1_relat_1 @ X37))),
% 2.65/2.84      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.65/2.84  thf('136', plain,
% 2.65/2.84      (![X35 : $i, X36 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.84          | ~ (v1_relat_1 @ X36))),
% 2.65/2.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.84  thf('137', plain,
% 2.65/2.84      (![X35 : $i, X36 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.84          | ~ (v1_relat_1 @ X36))),
% 2.65/2.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.84  thf('138', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.65/2.84  thf('139', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('sup+', [status(thm)], ['137', '138'])).
% 2.65/2.84  thf('140', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1)
% 2.65/2.84          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 2.65/2.84      inference('simplify', [status(thm)], ['139'])).
% 2.65/2.84  thf('141', plain,
% 2.65/2.84      (![X35 : $i, X36 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X36 @ X35) = (k5_relat_1 @ (k6_relat_1 @ X35) @ X36))
% 2.65/2.84          | ~ (v1_relat_1 @ X36))),
% 2.65/2.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.65/2.84  thf('142', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X1)
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['140', '141'])).
% 2.65/2.84  thf('143', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.84      inference('simplify', [status(thm)], ['58'])).
% 2.65/2.84  thf('144', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X1)
% 2.65/2.84              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.65/2.84      inference('clc', [status(thm)], ['142', '143'])).
% 2.65/2.84  thf('145', plain,
% 2.65/2.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 2.65/2.84            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ X10 @ X11)))
% 2.65/2.84          | ~ (v1_relat_1 @ X9))),
% 2.65/2.84      inference('cnf', [status(esa)], [t100_relat_1])).
% 2.65/2.84  thf('146', plain,
% 2.65/2.84      (![X37 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X37 @ (k1_relat_1 @ X37)) = (X37))
% 2.65/2.84          | ~ (v1_relat_1 @ X37))),
% 2.65/2.84      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.65/2.84  thf('147', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k7_relat_1 @ X1 @ 
% 2.65/2.84            (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.65/2.84            = (k7_relat_1 @ X1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['145', '146'])).
% 2.65/2.84  thf('148', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.84      inference('simplify', [status(thm)], ['58'])).
% 2.65/2.84  thf('149', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1)
% 2.65/2.84          | ((k7_relat_1 @ X1 @ 
% 2.65/2.84              (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.65/2.84              = (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.84      inference('clc', [status(thm)], ['147', '148'])).
% 2.65/2.84  thf('150', plain,
% 2.65/2.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 2.65/2.84            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ X10 @ X11)))
% 2.65/2.84          | ~ (v1_relat_1 @ X9))),
% 2.65/2.84      inference('cnf', [status(esa)], [t100_relat_1])).
% 2.65/2.84  thf('151', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 2.65/2.84            = (k7_relat_1 @ X2 @ 
% 2.65/2.84               (k3_xboole_0 @ X1 @ 
% 2.65/2.84                (k3_xboole_0 @ X0 @ 
% 2.65/2.84                 (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 2.65/2.84          | ~ (v1_relat_1 @ X2))),
% 2.65/2.84      inference('sup+', [status(thm)], ['149', '150'])).
% 2.65/2.84  thf('152', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.65/2.84      inference('simplify', [status(thm)], ['58'])).
% 2.65/2.84  thf('153', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X2)
% 2.65/2.84          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 2.65/2.84              = (k7_relat_1 @ X2 @ 
% 2.65/2.84                 (k3_xboole_0 @ X1 @ 
% 2.65/2.84                  (k3_xboole_0 @ X0 @ 
% 2.65/2.84                   (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))))))),
% 2.65/2.84      inference('clc', [status(thm)], ['151', '152'])).
% 2.65/2.84  thf('154', plain,
% 2.65/2.84      (![X33 : $i, X34 : $i]:
% 2.65/2.84         ((r1_tarski @ (k7_relat_1 @ X33 @ X34) @ X33) | ~ (v1_relat_1 @ X33))),
% 2.65/2.84      inference('cnf', [status(esa)], [t88_relat_1])).
% 2.65/2.84  thf('155', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X2)
% 2.65/2.84          | ~ (v1_relat_1 @ X2)
% 2.65/2.84          | ~ (v1_relat_1 @ X2))),
% 2.65/2.84      inference('sup+', [status(thm)], ['153', '154'])).
% 2.65/2.84  thf('156', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X2)
% 2.65/2.84          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X2))),
% 2.65/2.84      inference('simplify', [status(thm)], ['155'])).
% 2.65/2.84  thf('157', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['144', '156'])).
% 2.65/2.84  thf('158', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 2.65/2.84      inference('simplify', [status(thm)], ['157'])).
% 2.65/2.84  thf('159', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (r1_tarski @ X0 @ X1)
% 2.65/2.84          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['84', '85'])).
% 2.65/2.84  thf('160', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | ((k8_relat_1 @ X0 @ 
% 2.65/2.84              (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84              = (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 2.65/2.84      inference('sup-', [status(thm)], ['158', '159'])).
% 2.65/2.84  thf('161', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('162', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84            = (k8_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.65/2.84               (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['160', '161'])).
% 2.65/2.84  thf('163', plain,
% 2.65/2.84      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 2.65/2.84      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.65/2.84  thf('164', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.65/2.84            = (k8_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.65/2.84               (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['162', '163'])).
% 2.65/2.84  thf('165', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['67', '68'])).
% 2.65/2.84  thf('166', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['72', '73'])).
% 2.65/2.84  thf('167', plain,
% 2.65/2.84      (![X22 : $i, X23 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X22)
% 2.65/2.84          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 2.65/2.84          | ~ (r1_tarski @ X23 @ X22)
% 2.65/2.84          | ~ (v1_relat_1 @ X23))),
% 2.65/2.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 2.65/2.84  thf('168', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.65/2.84          | (r1_tarski @ 
% 2.65/2.84             (k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 2.65/2.84             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup-', [status(thm)], ['166', '167'])).
% 2.65/2.84  thf('169', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('170', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('171', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('172', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ X0)),
% 2.65/2.84      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 2.65/2.84  thf('173', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 2.65/2.84          (k3_xboole_0 @ X0 @ X1))),
% 2.65/2.84      inference('sup+', [status(thm)], ['165', '172'])).
% 2.65/2.84  thf('174', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((r1_tarski @ 
% 2.65/2.84           (k2_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 2.65/2.84           (k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['164', '173'])).
% 2.65/2.84  thf('175', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('176', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.65/2.84           (k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['174', '175'])).
% 2.65/2.84  thf('177', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (r1_tarski @ X0 @ X1)
% 2.65/2.84          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['84', '85'])).
% 2.65/2.84  thf('178', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | ((k8_relat_1 @ 
% 2.65/2.84              (k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 2.65/2.84              (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84              = (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 2.65/2.84      inference('sup-', [status(thm)], ['176', '177'])).
% 2.65/2.84  thf('179', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X2) @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['124', '125', '126'])).
% 2.65/2.84  thf('180', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X2) @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['124', '125', '126'])).
% 2.65/2.84  thf('181', plain,
% 2.65/2.84      (![X15 : $i, X16 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.84          | ~ (v1_relat_1 @ X15))),
% 2.65/2.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.84  thf('182', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k6_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['35', '36'])).
% 2.65/2.84  thf('183', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['181', '182'])).
% 2.65/2.84  thf('184', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('185', plain,
% 2.65/2.84      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['183', '184'])).
% 2.65/2.84  thf('186', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ 
% 2.65/2.84           (k6_relat_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))
% 2.65/2.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.84      inference('sup+', [status(thm)], ['180', '185'])).
% 2.65/2.84  thf('187', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ X0)),
% 2.65/2.84      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 2.65/2.84  thf('188', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 2.65/2.84          X0)),
% 2.65/2.84      inference('sup+', [status(thm)], ['186', '187'])).
% 2.65/2.84  thf('189', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('190', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.65/2.84      inference('demod', [status(thm)], ['188', '189'])).
% 2.65/2.84  thf('191', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (r1_tarski @ X0 @ X1)
% 2.65/2.84          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['84', '85'])).
% 2.65/2.84  thf('192', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.65/2.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.84      inference('sup-', [status(thm)], ['190', '191'])).
% 2.65/2.84  thf('193', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | ((k6_relat_1 @ 
% 2.65/2.84              (k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84              = (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['178', '179', '192'])).
% 2.65/2.84  thf('194', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('195', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k1_relat_1 @ (k6_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84            = (k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['193', '194'])).
% 2.65/2.84  thf('196', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('197', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.65/2.84            = (k3_xboole_0 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['195', '196'])).
% 2.65/2.84  thf('198', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84            = (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('sup+', [status(thm)], ['136', '197'])).
% 2.65/2.84  thf('199', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X1)
% 2.65/2.84          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84              = (k3_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.65/2.84      inference('simplify', [status(thm)], ['198'])).
% 2.65/2.84  thf('200', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)
% 2.65/2.84            = (k3_xboole_0 @ X0 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['135', '199'])).
% 2.65/2.84  thf('201', plain,
% 2.65/2.84      (![X32 : $i]:
% 2.65/2.84         (((k5_relat_1 @ X32 @ (k6_relat_1 @ (k2_relat_1 @ X32))) = (X32))
% 2.65/2.84          | ~ (v1_relat_1 @ X32))),
% 2.65/2.84      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.65/2.84  thf('202', plain,
% 2.65/2.84      (![X15 : $i, X16 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 2.65/2.84          | ~ (v1_relat_1 @ X15))),
% 2.65/2.84      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.65/2.84  thf('203', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['201', '202'])).
% 2.65/2.84  thf('204', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 2.65/2.84      inference('simplify', [status(thm)], ['203'])).
% 2.65/2.84  thf('205', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['50', '51'])).
% 2.65/2.84  thf('206', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 2.65/2.84      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.65/2.84  thf('207', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['205', '206'])).
% 2.65/2.84  thf('208', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k6_relat_1 @ (k3_xboole_0 @ X0 @ X0))
% 2.65/2.84            = (k8_relat_1 @ 
% 2.65/2.84               (k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X0))) @ 
% 2.65/2.84               (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['204', '207'])).
% 2.65/2.84  thf('209', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('210', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['67', '68'])).
% 2.65/2.84  thf('211', plain,
% 2.65/2.84      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['183', '184'])).
% 2.65/2.84  thf('212', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('213', plain,
% 2.65/2.84      (![X0 : $i]: ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)) = (k6_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['208', '209', '210', '211', '212'])).
% 2.65/2.84  thf('214', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('215', plain,
% 2.65/2.84      (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['213', '214'])).
% 2.65/2.84  thf('216', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 2.65/2.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.65/2.84  thf('217', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['215', '216'])).
% 2.65/2.84  thf('218', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['200', '217'])).
% 2.65/2.84  thf('219', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.65/2.84      inference('simplify', [status(thm)], ['218'])).
% 2.65/2.84  thf('220', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.65/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['116', '117'])).
% 2.65/2.84  thf('221', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (((k4_relat_1 @ X0)
% 2.65/2.84            = (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 2.65/2.84               (k6_relat_1 @ (k1_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ X0)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('sup+', [status(thm)], ['219', '220'])).
% 2.65/2.84  thf('222', plain,
% 2.65/2.84      (![X0 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ X0)
% 2.65/2.84          | ((k4_relat_1 @ X0)
% 2.65/2.84              = (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 2.65/2.84                 (k6_relat_1 @ (k1_relat_1 @ X0)))))),
% 2.65/2.84      inference('simplify', [status(thm)], ['221'])).
% 2.65/2.84  thf('223', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84            = (k5_relat_1 @ 
% 2.65/2.84               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 2.65/2.84               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['134', '222'])).
% 2.65/2.84  thf('224', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('225', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('226', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.65/2.84  thf('227', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.65/2.84  thf('228', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.65/2.84            (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 2.65/2.84            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.65/2.84               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['226', '227'])).
% 2.65/2.84  thf('229', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.65/2.84              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.65/2.84  thf('230', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('231', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 2.65/2.84           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.65/2.84              (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('demod', [status(thm)], ['228', '229', '230'])).
% 2.65/2.84  thf('232', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('233', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('234', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.65/2.84              (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 2.65/2.84      inference('demod', [status(thm)], ['231', '232', '233'])).
% 2.65/2.84  thf('235', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.65/2.84            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ X1))),
% 2.65/2.84      inference('demod', [status(thm)], ['116', '117'])).
% 2.65/2.84  thf('236', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84            = (k5_relat_1 @ 
% 2.65/2.84               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 2.65/2.84               (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['234', '235'])).
% 2.65/2.84  thf('237', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('238', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)], ['28', '29', '30', '63', '64', '65'])).
% 2.65/2.84  thf('239', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('240', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 2.65/2.84              (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 2.65/2.84  thf('241', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 2.65/2.84            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 2.65/2.84          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 2.65/2.84          | ~ (v1_relat_1 @ X1)
% 2.65/2.84          | ~ (v1_relat_1 @ X0))),
% 2.65/2.84      inference('demod', [status(thm)], ['92', '93'])).
% 2.65/2.84  thf('242', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.65/2.84          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84          | ((k8_relat_1 @ X2 @ 
% 2.65/2.84              (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 2.65/2.84               (k6_relat_1 @ X1)))
% 2.65/2.84              = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 2.65/2.84                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 2.65/2.84      inference('sup-', [status(thm)], ['240', '241'])).
% 2.65/2.84  thf('243', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('244', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 2.65/2.84      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.65/2.84  thf('245', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('246', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 2.65/2.84              (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 2.65/2.84  thf('247', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.65/2.84           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.65/2.84      inference('sup+', [status(thm)], ['104', '110'])).
% 2.65/2.84  thf('248', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['47', '52', '62'])).
% 2.65/2.84  thf('249', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.65/2.84           = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 2.65/2.84              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 2.65/2.84      inference('demod', [status(thm)],
% 2.65/2.84                ['242', '243', '244', '245', '246', '247', '248'])).
% 2.65/2.84  thf('250', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.65/2.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.65/2.84      inference('sup-', [status(thm)], ['190', '191'])).
% 2.65/2.84  thf('251', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.65/2.84      inference('demod', [status(thm)], ['60', '61'])).
% 2.65/2.84  thf('252', plain,
% 2.65/2.84      (![X0 : $i, X1 : $i]:
% 2.65/2.84         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.65/2.84           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.65/2.84      inference('demod', [status(thm)],
% 2.65/2.84                ['223', '224', '225', '249', '250', '251'])).
% 2.65/2.84  thf('253', plain,
% 2.65/2.84      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.65/2.84         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.65/2.84      inference('demod', [status(thm)], ['4', '252'])).
% 2.65/2.84  thf('254', plain, ($false), inference('simplify', [status(thm)], ['253'])).
% 2.65/2.84  
% 2.65/2.84  % SZS output end Refutation
% 2.65/2.84  
% 2.65/2.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
