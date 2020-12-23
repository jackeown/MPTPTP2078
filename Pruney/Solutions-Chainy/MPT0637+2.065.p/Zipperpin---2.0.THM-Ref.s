%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RqG95ue9w9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:05 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  176 (7160 expanded)
%              Number of leaves         :   25 (2472 expanded)
%              Depth                    :   34
%              Number of atoms          : 1582 (60816 expanded)
%              Number of equality atoms :  111 (4041 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
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
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('6',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('7',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X46: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X39 ) @ ( k4_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X46: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('15',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('24',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('25',plain,(
    ! [X49: $i] :
      ( ( ( k5_relat_1 @ X49 @ ( k6_relat_1 @ ( k2_relat_1 @ X49 ) ) )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k5_relat_1 @ X42 @ ( k5_relat_1 @ X41 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('36',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','37'])).

thf('39',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('50',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k5_relat_1 @ X42 @ ( k5_relat_1 @ X41 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('57',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','63'])).

thf('65',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('66',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','67'])).

thf('69',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','70'])).

thf('72',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','75'])).

thf('77',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('78',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('84',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('88',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X38 @ X37 ) ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('91',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('92',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('95',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X47 )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X46: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('98',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X39 ) @ ( k4_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('108',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) @ X34 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('111',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','112','113'])).

thf('115',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','85'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','85'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('121',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('122',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X47 )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('134',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('135',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','112','113'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','136','137'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','136','137'])).

thf('148',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','146','147'])).

thf('149',plain,(
    $false ),
    inference(simplify,[status(thm)],['148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RqG95ue9w9
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 453 iterations in 0.284s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.74  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.53/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(t94_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ B ) =>
% 0.53/0.74       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf(t43_funct_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.53/0.74       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i]:
% 0.53/0.74        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.53/0.74          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.53/0.74         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.53/0.74          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.53/0.74        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.74  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.53/0.74  thf('3', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.53/0.74         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.74  thf(t90_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ B ) =>
% 0.53/0.74       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.53/0.74         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X50 : $i, X51 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ X50 @ X51))
% 0.53/0.74            = (k3_xboole_0 @ (k1_relat_1 @ X50) @ X51))
% 0.53/0.74          | ~ (v1_relat_1 @ X50))),
% 0.53/0.74      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf(t72_relat_1, axiom,
% 0.53/0.74    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X46 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X46)) = (k6_relat_1 @ X46))),
% 0.53/0.74      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.74  thf(t54_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( v1_relat_1 @ B ) =>
% 0.53/0.74           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.53/0.74             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X39 : $i, X40 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X39)
% 0.53/0.74          | ((k4_relat_1 @ (k5_relat_1 @ X40 @ X39))
% 0.53/0.74              = (k5_relat_1 @ (k4_relat_1 @ X39) @ (k4_relat_1 @ X40)))
% 0.53/0.74          | ~ (v1_relat_1 @ X40))),
% 0.53/0.74      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.53/0.74  thf('11', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.53/0.74               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['7', '12'])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X46 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X46)) = (k6_relat_1 @ X46))),
% 0.53/0.74      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.74  thf('15', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('16', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.53/0.74            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.53/0.74  thf('21', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.53/0.74           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '22'])).
% 0.53/0.74  thf(t71_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.53/0.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.53/0.74  thf('24', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf(t80_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X49 : $i]:
% 0.53/0.74         (((k5_relat_1 @ X49 @ (k6_relat_1 @ (k2_relat_1 @ X49))) = (X49))
% 0.53/0.74          | ~ (v1_relat_1 @ X49))),
% 0.53/0.74      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.74            = (k6_relat_1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['24', '25'])).
% 0.53/0.74  thf('27', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.74           = (k6_relat_1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf(t55_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( v1_relat_1 @ B ) =>
% 0.53/0.74           ( ![C:$i]:
% 0.53/0.74             ( ( v1_relat_1 @ C ) =>
% 0.53/0.74               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.53/0.74                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X41)
% 0.53/0.74          | ((k5_relat_1 @ (k5_relat_1 @ X42 @ X41) @ X43)
% 0.53/0.74              = (k5_relat_1 @ X42 @ (k5_relat_1 @ X41 @ X43)))
% 0.53/0.74          | ~ (v1_relat_1 @ X43)
% 0.53/0.74          | ~ (v1_relat_1 @ X42))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.74               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['28', '29'])).
% 0.53/0.74  thf('31', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('32', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.74               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.74               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['23', '33'])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '22'])).
% 0.53/0.74  thf('36', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.74              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.74            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['6', '37'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.74           = (k6_relat_1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.74               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X1)
% 0.53/0.74          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.53/0.74  thf(dt_k5_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.53/0.74       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X31 : $i, X32 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X31)
% 0.53/0.74          | ~ (v1_relat_1 @ X32)
% 0.53/0.74          | (v1_relat_1 @ (k5_relat_1 @ X31 @ X32)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['44', '45'])).
% 0.53/0.74  thf('47', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.53/0.74      inference('demod', [status(thm)], ['46', '47'])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X31 : $i, X32 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X31)
% 0.53/0.74          | ~ (v1_relat_1 @ X32)
% 0.53/0.74          | (v1_relat_1 @ (k5_relat_1 @ X31 @ X32)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['49', '50'])).
% 0.53/0.74  thf('52', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['51', '52'])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.53/0.74      inference('simplify', [status(thm)], ['53'])).
% 0.53/0.74  thf('55', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X0)
% 0.53/0.74          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.53/0.74      inference('clc', [status(thm)], ['48', '54'])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X41)
% 0.53/0.74          | ((k5_relat_1 @ (k5_relat_1 @ X42 @ X41) @ X43)
% 0.53/0.74              = (k5_relat_1 @ X42 @ (k5_relat_1 @ X41 @ X43)))
% 0.53/0.74          | ~ (v1_relat_1 @ X43)
% 0.53/0.74          | ~ (v1_relat_1 @ X42))),
% 0.53/0.74      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (![X31 : $i, X32 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X31)
% 0.53/0.74          | ~ (v1_relat_1 @ X32)
% 0.53/0.74          | (v1_relat_1 @ (k5_relat_1 @ X31 @ X32)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.53/0.74  thf('58', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ X2)
% 0.53/0.74          | ~ (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['56', '57'])).
% 0.53/0.74  thf('59', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.53/0.74          | ~ (v1_relat_1 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ X2)
% 0.53/0.74          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['58'])).
% 0.53/0.74  thf('60', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X0)
% 0.53/0.74          | (v1_relat_1 @ 
% 0.53/0.74             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.53/0.74          | ~ (v1_relat_1 @ X2)
% 0.53/0.74          | ~ (v1_relat_1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['55', '59'])).
% 0.53/0.74  thf('61', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('62', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X0)
% 0.53/0.74          | (v1_relat_1 @ 
% 0.53/0.74             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 0.53/0.74          | ~ (v1_relat_1 @ X2)
% 0.53/0.74          | ~ (v1_relat_1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.74  thf('63', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X2)
% 0.53/0.74          | (v1_relat_1 @ 
% 0.53/0.74             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 0.53/0.74          | ~ (v1_relat_1 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['62'])).
% 0.53/0.74  thf('64', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['40', '63'])).
% 0.53/0.74  thf('65', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('66', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('67', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.53/0.74  thf('68', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['39', '67'])).
% 0.53/0.74  thf('69', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('70', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf('71', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.74           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['38', '70'])).
% 0.53/0.74  thf('72', plain,
% 0.53/0.74      (![X50 : $i, X51 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ X50 @ X51))
% 0.53/0.74            = (k3_xboole_0 @ (k1_relat_1 @ X50) @ X51))
% 0.53/0.74          | ~ (v1_relat_1 @ X50))),
% 0.53/0.74      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.74  thf('73', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74            = (k3_xboole_0 @ 
% 0.53/0.74               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['71', '72'])).
% 0.53/0.74  thf('74', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf('75', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k3_xboole_0 @ 
% 0.53/0.74              (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['73', '74'])).
% 0.53/0.74  thf('76', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74            = (k3_xboole_0 @ 
% 0.53/0.74               (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['5', '75'])).
% 0.53/0.74  thf('77', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('78', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('79', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.53/0.74  thf('80', plain,
% 0.53/0.74      (![X50 : $i, X51 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ X50 @ X51))
% 0.53/0.74            = (k3_xboole_0 @ (k1_relat_1 @ X50) @ X51))
% 0.53/0.74          | ~ (v1_relat_1 @ X50))),
% 0.53/0.74      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.74  thf('81', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.53/0.74  thf('82', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)
% 0.53/0.74            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['80', '81'])).
% 0.53/0.74  thf('83', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('84', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('85', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ X1 @ X0)
% 0.53/0.74           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.53/0.74  thf('86', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['79', '85'])).
% 0.53/0.74  thf('87', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.53/0.74           = (k6_relat_1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf(t45_relat_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( v1_relat_1 @ B ) =>
% 0.53/0.74           ( r1_tarski @
% 0.53/0.74             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.53/0.74  thf('88', plain,
% 0.53/0.74      (![X37 : $i, X38 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X37)
% 0.53/0.74          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X38 @ X37)) @ 
% 0.53/0.74             (k2_relat_1 @ X37))
% 0.53/0.74          | ~ (v1_relat_1 @ X38))),
% 0.53/0.74      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.53/0.74  thf('89', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.53/0.74           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['87', '88'])).
% 0.53/0.74  thf('90', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('91', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('92', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('93', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('94', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.53/0.74      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.53/0.74  thf(t77_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ B ) =>
% 0.53/0.74       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.53/0.74         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.53/0.74  thf('95', plain,
% 0.53/0.74      (![X47 : $i, X48 : $i]:
% 0.53/0.74         (~ (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 0.53/0.74          | ((k5_relat_1 @ (k6_relat_1 @ X48) @ X47) = (X47))
% 0.53/0.74          | ~ (v1_relat_1 @ X47))),
% 0.53/0.74      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.53/0.74  thf('96', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X0)
% 0.53/0.74          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['94', '95'])).
% 0.53/0.74  thf('97', plain,
% 0.53/0.74      (![X46 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X46)) = (k6_relat_1 @ X46))),
% 0.53/0.74      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.53/0.74  thf('98', plain,
% 0.53/0.74      (![X39 : $i, X40 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X39)
% 0.53/0.74          | ((k4_relat_1 @ (k5_relat_1 @ X40 @ X39))
% 0.53/0.74              = (k5_relat_1 @ (k4_relat_1 @ X39) @ (k4_relat_1 @ X40)))
% 0.53/0.74          | ~ (v1_relat_1 @ X40))),
% 0.53/0.74      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.53/0.74  thf('99', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.53/0.74            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('sup+', [status(thm)], ['97', '98'])).
% 0.53/0.74  thf('100', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('101', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.53/0.74            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.53/0.74  thf('102', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((k4_relat_1 @ X0)
% 0.53/0.74            = (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 0.53/0.74               (k6_relat_1 @ (k1_relat_1 @ X0))))
% 0.53/0.74          | ~ (v1_relat_1 @ X0)
% 0.53/0.74          | ~ (v1_relat_1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['96', '101'])).
% 0.53/0.74  thf('103', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X0)
% 0.53/0.74          | ((k4_relat_1 @ X0)
% 0.53/0.74              = (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 0.53/0.74                 (k6_relat_1 @ (k1_relat_1 @ X0)))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['102'])).
% 0.53/0.74  thf('104', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74            = (k5_relat_1 @ 
% 0.53/0.74               (k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.53/0.74               (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.53/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['86', '103'])).
% 0.53/0.74  thf('105', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.53/0.74           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('106', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.53/0.74           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.74  thf('107', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '22'])).
% 0.53/0.74  thf(t112_relat_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( v1_relat_1 @ B ) =>
% 0.53/0.74       ( ![C:$i]:
% 0.53/0.74         ( ( v1_relat_1 @ C ) =>
% 0.53/0.74           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.53/0.74             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.53/0.74  thf('108', plain,
% 0.53/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.53/0.74         (~ (v1_relat_1 @ X34)
% 0.53/0.74          | ((k7_relat_1 @ (k5_relat_1 @ X35 @ X34) @ X36)
% 0.53/0.74              = (k5_relat_1 @ (k7_relat_1 @ X35 @ X36) @ X34))
% 0.53/0.74          | ~ (v1_relat_1 @ X35))),
% 0.53/0.74      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.53/0.74  thf('109', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.53/0.74            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.53/0.74               (k6_relat_1 @ X1)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['107', '108'])).
% 0.53/0.74  thf('110', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('111', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('112', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.53/0.74           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.53/0.74              (k6_relat_1 @ X1)))),
% 0.53/0.74      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.53/0.74  thf('113', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf('114', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74           = (k7_relat_1 @ 
% 0.53/0.74              (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0) @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['104', '105', '106', '112', '113'])).
% 0.53/0.74  thf('115', plain,
% 0.53/0.74      (![X50 : $i, X51 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ X50 @ X51))
% 0.53/0.74            = (k3_xboole_0 @ (k1_relat_1 @ X50) @ X51))
% 0.53/0.74          | ~ (v1_relat_1 @ X50))),
% 0.53/0.74      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.74  thf('116', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74            = (k3_xboole_0 @ 
% 0.53/0.74               (k1_relat_1 @ 
% 0.53/0.74                (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X1)) @ 
% 0.53/0.74               X0))
% 0.53/0.74          | ~ (v1_relat_1 @ 
% 0.53/0.74               (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['114', '115'])).
% 0.53/0.74  thf('117', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['79', '85'])).
% 0.53/0.74  thf('118', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.53/0.74           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['79', '85'])).
% 0.53/0.74  thf('119', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ X1 @ X0)
% 0.53/0.74           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.53/0.74  thf(t17_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.74  thf('120', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.53/0.74      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.74  thf('121', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('122', plain,
% 0.53/0.74      (![X47 : $i, X48 : $i]:
% 0.53/0.74         (~ (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 0.53/0.74          | ((k5_relat_1 @ (k6_relat_1 @ X48) @ X47) = (X47))
% 0.53/0.74          | ~ (v1_relat_1 @ X47))),
% 0.53/0.74      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.53/0.74  thf('123', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.53/0.74          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.53/0.74              = (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['121', '122'])).
% 0.53/0.74  thf('124', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('125', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.74          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.53/0.74              = (k6_relat_1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['123', '124'])).
% 0.53/0.74  thf('126', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.53/0.74           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.53/0.74           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['120', '125'])).
% 0.53/0.74  thf('127', plain,
% 0.53/0.74      (![X52 : $i, X53 : $i]:
% 0.53/0.74         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 0.53/0.74          | ~ (v1_relat_1 @ X53))),
% 0.53/0.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.53/0.74  thf('128', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.53/0.74            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['126', '127'])).
% 0.53/0.74  thf('129', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('130', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.53/0.74           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['128', '129'])).
% 0.53/0.74  thf('131', plain,
% 0.53/0.74      (![X50 : $i, X51 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k7_relat_1 @ X50 @ X51))
% 0.53/0.74            = (k3_xboole_0 @ (k1_relat_1 @ X50) @ X51))
% 0.53/0.74          | ~ (v1_relat_1 @ X50))),
% 0.53/0.74      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.74  thf('132', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.53/0.74            = (k3_xboole_0 @ 
% 0.53/0.74               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ X1))
% 0.53/0.74          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['130', '131'])).
% 0.53/0.74  thf('133', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('134', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.53/0.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.53/0.74  thf('135', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.74  thf('136', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ X1 @ X0)
% 0.53/0.74           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 0.53/0.74  thf('137', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.74  thf('138', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)],
% 0.53/0.74                ['116', '117', '118', '119', '136', '137'])).
% 0.53/0.74  thf('139', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.53/0.74           = (k7_relat_1 @ 
% 0.53/0.74              (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0) @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['104', '105', '106', '112', '113'])).
% 0.53/0.74  thf('140', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.74           = (k7_relat_1 @ 
% 0.53/0.74              (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['138', '139'])).
% 0.53/0.74  thf('141', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.53/0.74           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['128', '129'])).
% 0.53/0.74  thf('142', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.74           = (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['140', '141'])).
% 0.53/0.74  thf('143', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)],
% 0.53/0.74                ['116', '117', '118', '119', '136', '137'])).
% 0.53/0.74  thf('144', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.53/0.74           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['128', '129'])).
% 0.53/0.74  thf('145', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 0.53/0.74           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['143', '144'])).
% 0.53/0.74  thf('146', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.53/0.74           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['142', '145'])).
% 0.53/0.74  thf('147', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)],
% 0.53/0.74                ['116', '117', '118', '119', '136', '137'])).
% 0.53/0.74  thf('148', plain,
% 0.53/0.74      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.53/0.74         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('demod', [status(thm)], ['4', '146', '147'])).
% 0.53/0.74  thf('149', plain, ($false), inference('simplify', [status(thm)], ['148'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
