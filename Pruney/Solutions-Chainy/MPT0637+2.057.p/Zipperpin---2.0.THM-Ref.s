%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4XzMNacFG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:04 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  167 (5380 expanded)
%              Number of leaves         :   27 (1860 expanded)
%              Depth                    :   32
%              Number of atoms          : 1441 (45164 expanded)
%              Number of equality atoms :  101 (3353 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
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
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
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
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('7',plain,(
    ! [X51: $i] :
      ( ( ( k5_relat_1 @ X51 @ ( k6_relat_1 @ ( k2_relat_1 @ X51 ) ) )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('18',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X56 ) @ X57 )
      | ( ( k7_relat_1 @ X56 @ X57 )
        = X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('21',plain,(
    ! [X46: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X42 ) @ ( k4_relat_1 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) @ X37 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','43'])).

thf('45',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('47',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ X55 @ X54 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('54',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('55',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X42 ) @ ( k4_relat_1 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','65'])).

thf('67',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','69'])).

thf('71',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('78',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('82',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X47 )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X46: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('85',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X42 ) @ ( k4_relat_1 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('90',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X1 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('103',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( ( k5_relat_1 @ X49 @ ( k6_relat_1 @ X50 ) )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('114',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X56 ) @ X57 )
      | ( ( k7_relat_1 @ X56 @ X57 )
        = X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('123',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','125','126'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','125','126'])).

thf('137',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','135','136'])).

thf('138',plain,(
    $false ),
    inference(simplify,[status(thm)],['137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4XzMNacFG
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:58:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 929 iterations in 0.521s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.97  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.75/0.97  thf(t94_relat_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ B ) =>
% 0.75/0.97       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.75/0.97  thf('0', plain,
% 0.75/0.97      (![X54 : $i, X55 : $i]:
% 0.75/0.97         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.75/0.97          | ~ (v1_relat_1 @ X55))),
% 0.75/0.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.75/0.97  thf(t43_funct_1, conjecture,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.75/0.97       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i]:
% 0.75/0.97        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.75/0.97          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.75/0.97         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.75/0.97          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.75/0.97        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.97  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.75/0.97  thf('3', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('4', plain,
% 0.75/0.97      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.75/0.97         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('demod', [status(thm)], ['2', '3'])).
% 0.75/0.97  thf(t90_relat_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ B ) =>
% 0.75/0.97       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.75/0.97         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      (![X52 : $i, X53 : $i]:
% 0.75/0.97         (((k1_relat_1 @ (k7_relat_1 @ X52 @ X53))
% 0.75/0.97            = (k3_xboole_0 @ (k1_relat_1 @ X52) @ X53))
% 0.75/0.97          | ~ (v1_relat_1 @ X52))),
% 0.75/0.97      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.75/0.97  thf(t71_relat_1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.75/0.97       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.75/0.97  thf('6', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.75/0.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.97  thf(t80_relat_1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.75/0.97  thf('7', plain,
% 0.75/0.97      (![X51 : $i]:
% 0.75/0.97         (((k5_relat_1 @ X51 @ (k6_relat_1 @ (k2_relat_1 @ X51))) = (X51))
% 0.75/0.97          | ~ (v1_relat_1 @ X51))),
% 0.75/0.97      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.75/0.97            = (k6_relat_1 @ X0))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['6', '7'])).
% 0.75/0.97  thf('9', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.75/0.97           = (k6_relat_1 @ X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['8', '9'])).
% 0.75/0.97  thf(t45_relat_1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ![B:$i]:
% 0.75/0.97         ( ( v1_relat_1 @ B ) =>
% 0.75/0.97           ( r1_tarski @
% 0.75/0.97             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.75/0.97  thf('11', plain,
% 0.75/0.97      (![X40 : $i, X41 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X40)
% 0.75/0.97          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X41 @ X40)) @ 
% 0.75/0.97             (k2_relat_1 @ X40))
% 0.75/0.97          | ~ (v1_relat_1 @ X41))),
% 0.75/0.97      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.75/0.97  thf('12', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.75/0.97           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.97  thf('13', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.75/0.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.97  thf('14', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.75/0.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.97  thf('15', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('16', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('17', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.97      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.75/0.97  thf(t97_relat_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ B ) =>
% 0.75/0.97       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.75/0.97         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.75/0.97  thf('18', plain,
% 0.75/0.97      (![X56 : $i, X57 : $i]:
% 0.75/0.97         (~ (r1_tarski @ (k1_relat_1 @ X56) @ X57)
% 0.75/0.97          | ((k7_relat_1 @ X56 @ X57) = (X56))
% 0.75/0.97          | ~ (v1_relat_1 @ X56))),
% 0.75/0.97      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.75/0.97  thf('19', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      (![X54 : $i, X55 : $i]:
% 0.75/0.97         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.75/0.97          | ~ (v1_relat_1 @ X55))),
% 0.75/0.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.75/0.97  thf(t72_relat_1, axiom,
% 0.75/0.97    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      (![X46 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X46)) = (k6_relat_1 @ X46))),
% 0.75/0.97      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (![X46 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X46)) = (k6_relat_1 @ X46))),
% 0.75/0.97      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.75/0.97  thf(t54_relat_1, axiom,
% 0.75/0.97    (![A:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ A ) =>
% 0.75/0.97       ( ![B:$i]:
% 0.75/0.97         ( ( v1_relat_1 @ B ) =>
% 0.75/0.97           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.75/0.97             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      (![X42 : $i, X43 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X42)
% 0.75/0.97          | ((k4_relat_1 @ (k5_relat_1 @ X43 @ X42))
% 0.75/0.97              = (k5_relat_1 @ (k4_relat_1 @ X42) @ (k4_relat_1 @ X43)))
% 0.75/0.97          | ~ (v1_relat_1 @ X43))),
% 0.75/0.97      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.97            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.75/0.97          | ~ (v1_relat_1 @ X1)
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['22', '23'])).
% 0.75/0.97  thf('25', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('26', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.75/0.97            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.75/0.97          | ~ (v1_relat_1 @ X1))),
% 0.75/0.97      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.97  thf('27', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.75/0.97            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['21', '26'])).
% 0.75/0.97  thf('28', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('29', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.75/0.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.97  thf('30', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.97            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['20', '29'])).
% 0.75/0.97  thf('31', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('32', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('33', plain,
% 0.75/0.97      (![X54 : $i, X55 : $i]:
% 0.75/0.97         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.75/0.97          | ~ (v1_relat_1 @ X55))),
% 0.75/0.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.75/0.97  thf('34', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('35', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.97            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['33', '34'])).
% 0.75/0.97  thf('36', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('37', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.97           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.97  thf('38', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.75/0.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['32', '37'])).
% 0.75/0.97  thf(t112_relat_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( v1_relat_1 @ B ) =>
% 0.75/0.97       ( ![C:$i]:
% 0.75/0.97         ( ( v1_relat_1 @ C ) =>
% 0.75/0.97           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.75/0.97             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.75/0.97  thf('39', plain,
% 0.75/0.97      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.75/0.97         (~ (v1_relat_1 @ X35)
% 0.75/0.97          | ((k7_relat_1 @ (k5_relat_1 @ X36 @ X35) @ X37)
% 0.75/0.97              = (k5_relat_1 @ (k7_relat_1 @ X36 @ X37) @ X35))
% 0.75/0.97          | ~ (v1_relat_1 @ X36))),
% 0.75/0.97      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.75/0.97  thf('40', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.75/0.97            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.75/0.97               (k6_relat_1 @ X1)))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['38', '39'])).
% 0.75/0.97  thf('41', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.97  thf('42', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.75/0.98           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.75/0.98              (k6_relat_1 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.75/0.98            (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.75/0.98            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['19', '43'])).
% 0.75/0.98  thf('45', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.75/0.98           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['32', '37'])).
% 0.75/0.98  thf('47', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 0.75/0.98           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (![X52 : $i, X53 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ X52 @ X53))
% 0.75/0.98            = (k3_xboole_0 @ (k1_relat_1 @ X52) @ X53))
% 0.75/0.98          | ~ (v1_relat_1 @ X52))),
% 0.75/0.98      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.75/0.98  thf('50', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98            = (k3_xboole_0 @ 
% 0.75/0.98               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.98  thf('51', plain,
% 0.75/0.98      (![X54 : $i, X55 : $i]:
% 0.75/0.98         (((k7_relat_1 @ X55 @ X54) = (k5_relat_1 @ (k6_relat_1 @ X54) @ X55))
% 0.75/0.98          | ~ (v1_relat_1 @ X55))),
% 0.75/0.98      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.75/0.98           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.98  thf(dt_k4_relat_1, axiom,
% 0.75/0.98    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.75/0.98  thf('53', plain,
% 0.75/0.98      (![X31 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X31)) | ~ (v1_relat_1 @ X31))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (![X31 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X31)) | ~ (v1_relat_1 @ X31))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X42 : $i, X43 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X42)
% 0.75/0.98          | ((k4_relat_1 @ (k5_relat_1 @ X43 @ X42))
% 0.75/0.98              = (k5_relat_1 @ (k4_relat_1 @ X42) @ (k4_relat_1 @ X43)))
% 0.75/0.98          | ~ (v1_relat_1 @ X43))),
% 0.75/0.98      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.75/0.98  thf(dt_k5_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.75/0.98       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X32 : $i, X33 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X32)
% 0.75/0.98          | ~ (v1_relat_1 @ X33)
% 0.75/0.98          | (v1_relat_1 @ (k5_relat_1 @ X32 @ X33)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.75/0.98          | ~ (v1_relat_1 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 0.75/0.98          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['55', '56'])).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 0.75/0.98          | ~ (v1_relat_1 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['54', '57'])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.75/0.98          | ~ (v1_relat_1 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['58'])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | ~ (v1_relat_1 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['53', '59'])).
% 0.75/0.98  thf('61', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.75/0.98          | ~ (v1_relat_1 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['60'])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['52', '61'])).
% 0.75/0.98  thf('63', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('64', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.75/0.98  thf('66', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['51', '65'])).
% 0.75/0.98  thf('67', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('68', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98           = (k3_xboole_0 @ 
% 0.75/0.98              (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['50', '68'])).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98            = (k3_xboole_0 @ 
% 0.75/0.98               (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['5', '69'])).
% 0.75/0.98  thf('71', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('72', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('73', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.75/0.98  thf('74', plain,
% 0.75/0.98      (![X52 : $i, X53 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ X52 @ X53))
% 0.75/0.98            = (k3_xboole_0 @ (k1_relat_1 @ X52) @ X53))
% 0.75/0.98          | ~ (v1_relat_1 @ X52))),
% 0.75/0.98      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.75/0.98  thf('75', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.75/0.98  thf('76', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)
% 0.75/0.98            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['74', '75'])).
% 0.75/0.98  thf('77', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('78', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('79', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.75/0.98  thf('80', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['73', '79'])).
% 0.75/0.98  thf('81', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.98      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.75/0.98  thf(t77_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ B ) =>
% 0.75/0.98       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.75/0.98         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.75/0.98  thf('82', plain,
% 0.75/0.98      (![X47 : $i, X48 : $i]:
% 0.75/0.98         (~ (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 0.75/0.98          | ((k5_relat_1 @ (k6_relat_1 @ X48) @ X47) = (X47))
% 0.75/0.98          | ~ (v1_relat_1 @ X47))),
% 0.75/0.98      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.75/0.98  thf('83', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['81', '82'])).
% 0.75/0.98  thf('84', plain,
% 0.75/0.98      (![X46 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X46)) = (k6_relat_1 @ X46))),
% 0.75/0.98      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.75/0.98  thf('85', plain,
% 0.75/0.98      (![X42 : $i, X43 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X42)
% 0.75/0.98          | ((k4_relat_1 @ (k5_relat_1 @ X43 @ X42))
% 0.75/0.98              = (k5_relat_1 @ (k4_relat_1 @ X42) @ (k4_relat_1 @ X43)))
% 0.75/0.98          | ~ (v1_relat_1 @ X43))),
% 0.75/0.98      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.75/0.98  thf('86', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.98            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['84', '85'])).
% 0.75/0.98  thf('87', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('88', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.98            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.75/0.98          | ~ (v1_relat_1 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('89', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('90', plain,
% 0.75/0.98      (![X40 : $i, X41 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X40)
% 0.75/0.98          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X41 @ X40)) @ 
% 0.75/0.98             (k2_relat_1 @ X40))
% 0.75/0.98          | ~ (v1_relat_1 @ X41))),
% 0.75/0.98      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.75/0.98  thf('91', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.75/0.98           X0)
% 0.75/0.98          | ~ (v1_relat_1 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['89', '90'])).
% 0.75/0.98  thf('92', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('93', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.75/0.98           X0)
% 0.75/0.98          | ~ (v1_relat_1 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['91', '92'])).
% 0.75/0.98  thf('94', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r1_tarski @ 
% 0.75/0.98           (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.75/0.98           X1)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['88', '93'])).
% 0.75/0.98  thf('95', plain,
% 0.75/0.98      (![X31 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X31)) | ~ (v1_relat_1 @ X31))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.75/0.98  thf('96', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | (r1_tarski @ 
% 0.75/0.98             (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.75/0.98             X1))),
% 0.75/0.98      inference('clc', [status(thm)], ['94', '95'])).
% 0.75/0.98  thf('97', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['83', '96'])).
% 0.75/0.98  thf('98', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X0)
% 0.75/0.98          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['97'])).
% 0.75/0.98  thf('99', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r1_tarski @ 
% 0.75/0.98           (k2_relat_1 @ (k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 0.75/0.98           (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['80', '98'])).
% 0.75/0.98  thf('100', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.98           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.98  thf('101', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('102', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.75/0.98          (k3_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.75/0.98  thf(t79_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ B ) =>
% 0.75/0.98       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.75/0.98         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.75/0.98  thf('103', plain,
% 0.75/0.98      (![X49 : $i, X50 : $i]:
% 0.75/0.98         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 0.75/0.98          | ((k5_relat_1 @ X49 @ (k6_relat_1 @ X50)) = (X49))
% 0.75/0.98          | ~ (v1_relat_1 @ X49))),
% 0.75/0.98      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.75/0.98  thf('104', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.75/0.98          | ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.75/0.98              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.75/0.98              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['102', '103'])).
% 0.75/0.98  thf('105', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('106', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 0.75/0.98           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.75/0.98              (k6_relat_1 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.75/0.98  thf('107', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ 
% 0.75/0.98           (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0) @ X1)
% 0.75/0.98           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.75/0.98  thf('108', plain,
% 0.75/0.98      (![X52 : $i, X53 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ X52 @ X53))
% 0.75/0.98            = (k3_xboole_0 @ (k1_relat_1 @ X52) @ X53))
% 0.75/0.98          | ~ (v1_relat_1 @ X52))),
% 0.75/0.98      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.75/0.98  thf('109', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98            = (k3_xboole_0 @ 
% 0.75/0.98               (k1_relat_1 @ 
% 0.75/0.98                (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X1)) @ 
% 0.75/0.98               X0))
% 0.75/0.98          | ~ (v1_relat_1 @ 
% 0.75/0.98               (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['107', '108'])).
% 0.75/0.98  thf('110', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['73', '79'])).
% 0.75/0.98  thf('111', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['73', '79'])).
% 0.75/0.98  thf('112', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.75/0.98  thf(t17_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.98  thf('113', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.75/0.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.98  thf('114', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('115', plain,
% 0.75/0.98      (![X56 : $i, X57 : $i]:
% 0.75/0.98         (~ (r1_tarski @ (k1_relat_1 @ X56) @ X57)
% 0.75/0.98          | ((k7_relat_1 @ X56 @ X57) = (X56))
% 0.75/0.98          | ~ (v1_relat_1 @ X56))),
% 0.75/0.98      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.75/0.98  thf('116', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.98          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['114', '115'])).
% 0.75/0.98  thf('117', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('118', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X0 @ X1)
% 0.75/0.98          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['116', '117'])).
% 0.75/0.98  thf('119', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 0.75/0.98           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['113', '118'])).
% 0.75/0.98  thf('120', plain,
% 0.75/0.98      (![X52 : $i, X53 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k7_relat_1 @ X52 @ X53))
% 0.75/0.98            = (k3_xboole_0 @ (k1_relat_1 @ X52) @ X53))
% 0.75/0.98          | ~ (v1_relat_1 @ X52))),
% 0.75/0.98      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.75/0.98  thf('121', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.75/0.98            = (k3_xboole_0 @ 
% 0.75/0.98               (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ X1))
% 0.75/0.98          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.75/0.98      inference('sup+', [status(thm)], ['119', '120'])).
% 0.75/0.98  thf('122', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('123', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.98  thf('124', plain, (![X34 : $i]: (v1_relat_1 @ (k6_relat_1 @ X34))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/0.98  thf('125', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.75/0.98  thf('126', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['66', '67'])).
% 0.75/0.98  thf('127', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)],
% 0.75/0.98                ['109', '110', '111', '112', '125', '126'])).
% 0.75/0.98  thf('128', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ 
% 0.75/0.98           (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0) @ X1)
% 0.75/0.98           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.75/0.98  thf('129', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ 
% 0.75/0.98           (k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ X0)
% 0.75/0.98           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['127', '128'])).
% 0.75/0.98  thf('130', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 0.75/0.98           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['113', '118'])).
% 0.75/0.98  thf('131', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 0.75/0.98           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['129', '130'])).
% 0.75/0.98  thf('132', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)],
% 0.75/0.98                ['109', '110', '111', '112', '125', '126'])).
% 0.75/0.98  thf('133', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 0.75/0.98           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['113', '118'])).
% 0.75/0.98  thf('134', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 0.75/0.98           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['132', '133'])).
% 0.75/0.98  thf('135', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.75/0.98           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['131', '134'])).
% 0.75/0.98  thf('136', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)],
% 0.75/0.98                ['109', '110', '111', '112', '125', '126'])).
% 0.75/0.98  thf('137', plain,
% 0.75/0.98      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.75/0.98         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('demod', [status(thm)], ['4', '135', '136'])).
% 0.75/0.98  thf('138', plain, ($false), inference('simplify', [status(thm)], ['137'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
