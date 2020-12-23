%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0472+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YA72tcMwf8

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   47 (  76 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 419 expanded)
%              Number of equality atoms :   37 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(t64_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( ( k1_relat_1 @ A )
              = k1_xboole_0 )
            | ( ( k2_relat_1 @ A )
              = k1_xboole_0 ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_relat_1])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A_5 )
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
    ( ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X2104: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X2104 ) )
      | ~ ( v1_relat_1 @ X2104 )
      | ( v1_xboole_0 @ X2104 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('6',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_5 )
      | ~ ( v1_relat_1 @ sk_A_5 ) )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A_5 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7','10','11'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A_5 = o_0_0_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_A_5 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    sk_A_5 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k1_relat_1 @ sk_A_5 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_A_5 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_5 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_A_5 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_A_5 )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['3','22'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X2105: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X2105 ) )
      | ~ ( v1_relat_1 @ X2105 )
      | ( v1_xboole_0 @ X2105 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A_5 )
    | ~ ( v1_relat_1 @ sk_A_5 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('27',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ sk_A_5 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    sk_A_5 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A_5 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
