%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0752+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1pkVhHmOcU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 109 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 428 expanded)
%              Number of equality atoms :    7 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ ( k1_xboole_0 @ A ) )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ ( k1_xboole_0 @ A ) )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ ( k1_xboole_0 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,
    ( ~ ( v5_ordinal1 @ o_0_0_xboole_0 )
    | ~ ( v1_funct_1 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
    | ~ ( v5_relat_1 @ ( o_0_0_xboole_0 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['0','1','2','3','4'])).

thf('6',plain,
    ( ~ ( v5_ordinal1 @ o_0_0_xboole_0 )
   <= ~ ( v5_ordinal1 @ o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('10',plain,(
    ! [X3067: $i] :
      ( ( v5_ordinal1 @ X3067 )
      | ~ ( v1_xboole_0 @ X3067 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

thf('11',plain,(
    v5_ordinal1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( $false
   <= ~ ( v5_ordinal1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X2038: $i] :
      ( ( v1_relat_1 @ X2038 )
      | ~ ( v1_xboole_0 @ X2038 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ o_0_0_xboole_0 )
   <= ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ ( k1_xboole_0 @ B ) )
      & ( v4_relat_1 @ ( k1_xboole_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X2187: $i] :
      ( v5_relat_1 @ ( k1_xboole_0 @ X2187 ) ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X2187: $i] :
      ( v5_relat_1 @ ( o_0_0_xboole_0 @ X2187 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v5_relat_1 @ ( o_0_0_xboole_0 @ sk_A_14 ) )
   <= ~ ( v5_relat_1 @ ( o_0_0_xboole_0 @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('22',plain,(
    v5_relat_1 @ ( o_0_0_xboole_0 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('23',plain,(
    ! [X2618: $i] :
      ( ( v1_funct_1 @ X2618 )
      | ~ ( v1_xboole_0 @ X2618 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ o_0_0_xboole_0 )
   <= ~ ( v1_funct_1 @ o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ~ ( v1_funct_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('27',plain,(
    v1_funct_1 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v5_ordinal1 @ o_0_0_xboole_0 )
    | ~ ( v1_funct_1 @ o_0_0_xboole_0 )
    | ~ ( v5_relat_1 @ ( o_0_0_xboole_0 @ sk_A_14 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,(
    ~ ( v5_ordinal1 @ o_0_0_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['17','22','27','28'])).

thf('30',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['12','29'])).

%------------------------------------------------------------------------------
