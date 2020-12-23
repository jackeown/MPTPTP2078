%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0658+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dbi9TGZmxW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 108 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 816 expanded)
%              Number of equality atoms :   19 (  69 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X2186: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X2186 ) )
        = X2186 )
      | ~ ( v1_relat_1 @ X2186 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t65_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_1])).

thf('1',plain,(
    ( k2_funct_1 @ ( k2_funct_1 @ sk_A_8 ) )
 != sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2632: $i] :
      ( ~ ( v2_funct_1 @ X2632 )
      | ( ( k2_funct_1 @ X2632 )
        = ( k4_relat_1 @ X2632 ) )
      | ~ ( v1_funct_1 @ X2632 )
      | ~ ( v1_relat_1 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_A_8 )
    | ( ( k2_funct_1 @ sk_A_8 )
      = ( k4_relat_1 @ sk_A_8 ) )
    | ~ ( v2_funct_1 @ sk_A_8 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_1 @ sk_A_8 )
    = ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ( k2_funct_1 @ ( k4_relat_1 @ sk_A_8 ) )
 != sk_A_8 ),
    inference(demod,[status(thm)],['1','7'])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_A_8 )
    = ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X2633: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2633 ) )
      | ~ ( v1_funct_1 @ X2633 )
      | ~ ( v1_relat_1 @ X2633 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('11',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A_8 ) )
    | ~ ( v1_relat_1 @ sk_A_8 )
    | ~ ( v1_funct_1 @ sk_A_8 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X2632: $i] :
      ( ~ ( v2_funct_1 @ X2632 )
      | ( ( k2_funct_1 @ X2632 )
        = ( k4_relat_1 @ X2632 ) )
      | ~ ( v1_funct_1 @ X2632 )
      | ~ ( v1_relat_1 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A_8 ) )
    | ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A_8 ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_A_8 ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A_8 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_funct_1 @ sk_A_8 )
    = ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('18',plain,(
    ! [X2633: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2633 ) )
      | ~ ( v1_funct_1 @ X2633 )
      | ~ ( v1_relat_1 @ X2633 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A_8 ) )
    | ~ ( v1_relat_1 @ sk_A_8 )
    | ~ ( v1_funct_1 @ sk_A_8 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k2_funct_1 @ sk_A_8 )
    = ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X2653: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2653 ) )
      | ~ ( v2_funct_1 @ X2653 )
      | ~ ( v1_funct_1 @ X2653 )
      | ~ ( v1_relat_1 @ X2653 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('25',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_A_8 ) )
    | ~ ( v1_relat_1 @ sk_A_8 )
    | ~ ( v1_funct_1 @ sk_A_8 )
    | ~ ( v2_funct_1 @ sk_A_8 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A_8 ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A_8 ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A_8 ) ) ),
    inference(demod,[status(thm)],['16','22','29'])).

thf('31',plain,(
    ( k4_relat_1 @ ( k4_relat_1 @ sk_A_8 ) )
 != sk_A_8 ),
    inference(demod,[status(thm)],['8','30'])).

thf('32',plain,
    ( ( sk_A_8 != sk_A_8 )
    | ~ ( v1_relat_1 @ sk_A_8 ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_A_8 != sk_A_8 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
