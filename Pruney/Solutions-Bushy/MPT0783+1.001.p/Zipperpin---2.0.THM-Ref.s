%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SOqxhDhS4C

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:29 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   66 (  93 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  471 ( 717 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(t22_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v1_relat_2 @ B )
       => ( v1_relat_2 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_2 @ X3 )
      | ( v1_relat_2 @ ( k2_wellord1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t22_wellord1])).

thf(t24_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v8_relat_2 @ B )
       => ( v8_relat_2 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v8_relat_2 @ X7 )
      | ( v8_relat_2 @ ( k2_wellord1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t24_wellord1])).

thf(t25_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_2 @ B )
       => ( v4_relat_2 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_2 @ X9 )
      | ( v4_relat_2 @ ( k2_wellord1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t25_wellord1])).

thf(t23_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v6_relat_2 @ B )
       => ( v6_relat_2 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v6_relat_2 @ X5 )
      | ( v6_relat_2 @ ( k2_wellord1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t23_wellord1])).

thf(t31_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v1_wellord1 @ B )
       => ( v1_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_wellord1 @ X11 )
      | ( v1_wellord1 @ ( k2_wellord1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_wellord1])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v6_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v6_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v6_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v4_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v4_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v8_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v4_relat_2 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v4_relat_2 @ X1 )
      | ~ ( v8_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v8_relat_2 @ X1 )
      | ~ ( v4_relat_2 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v1_wellord1 @ X1 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_wellord1 @ X1 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v4_relat_2 @ X1 )
      | ~ ( v8_relat_2 @ X1 )
      | ~ ( v1_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t32_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( v2_wellord1 @ B )
         => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_wellord1])).

thf('18',plain,(
    ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v1_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('23',plain,
    ( ( v1_relat_2 @ sk_B )
    | ~ ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_wellord1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('28',plain,
    ( ( v8_relat_2 @ sk_B )
    | ~ ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_wellord1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v8_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('33',plain,
    ( ( v4_relat_2 @ sk_B )
    | ~ ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_wellord1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('38',plain,
    ( ( v6_relat_2 @ sk_B )
    | ~ ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_wellord1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v6_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('43',plain,
    ( ( v1_wellord1 @ sk_B )
    | ~ ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_wellord1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_wellord1 @ sk_B ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20','25','30','35','40','45'])).


%------------------------------------------------------------------------------
