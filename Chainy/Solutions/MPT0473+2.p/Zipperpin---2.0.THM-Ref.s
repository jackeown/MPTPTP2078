%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0473+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OBj9JUgytq

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 141 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  310 ( 808 expanded)
%              Number of equality atoms :   61 ( 171 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t65_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
        <=> ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_relat_1])).

thf('0',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
      = o_0_0_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_5 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_relat_1 @ sk_A_5 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A_5 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,
    ( ( ( k1_relat_1 @ sk_A_5 )
      = o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X2104: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X2104 ) )
      | ~ ( v1_relat_1 @ X2104 )
      | ( v1_xboole_0 @ X2104 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ sk_A_5 )
      | ~ ( v1_relat_1 @ sk_A_5 ) )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A_5 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A_5 = o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_5 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A_5 )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A_5 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k2_relat_1 @ sk_A_5 )
       != k1_xboole_0 )
      & ( ( k1_relat_1 @ sk_A_5 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_5 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_A_5 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['5','28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_A_5 )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['3','30'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X2105: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X2105 ) )
      | ~ ( v1_relat_1 @ X2105 )
      | ( v1_xboole_0 @ X2105 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A_5 )
    | ~ ( v1_relat_1 @ sk_A_5 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('35',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_xboole_0 @ sk_A_5 ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X2088: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X2088 ) )
      | ~ ( v1_xboole_0 @ X2088 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('38',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_A_5 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_A_5 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_A_5 )
     != o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_relat_1 @ sk_A_5 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['5','28'])).

thf('45',plain,(
    ( k1_relat_1 @ sk_A_5 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','45'])).

%------------------------------------------------------------------------------
