%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ljZtpQymPZ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 215 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  903 (1665 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(r1_wellord1_type,type,(
    r1_wellord1: $i > $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t8_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) )
      <=> ( v2_wellord1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        <=> ( v2_wellord1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_wellord1])).

thf('0',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v2_wellord1 @ sk_A )
    | ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d5_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_wellord1 @ A @ B )
        <=> ( ( r1_relat_2 @ A @ B )
            & ( r8_relat_2 @ A @ B )
            & ( r4_relat_2 @ A @ B )
            & ( r6_relat_2 @ A @ B )
            & ( r1_wellord1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r1_wellord1 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('5',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t5_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_wellord1 @ A )
      <=> ( r1_wellord1 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ~ ( r1_wellord1 @ X8 @ ( k3_relat_1 @ X8 ) )
      | ( v1_wellord1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v1_wellord1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_wellord1 @ sk_A )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_2 @ X3 )
      | ~ ( v8_relat_2 @ X3 )
      | ~ ( v4_relat_2 @ X3 )
      | ~ ( v6_relat_2 @ X3 )
      | ~ ( v1_wellord1 @ X3 )
      | ( v2_wellord1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('14',plain,
    ( ( v2_wellord1 @ sk_A )
    | ~ ( v1_wellord1 @ sk_A )
    | ~ ( v6_relat_2 @ sk_A )
    | ~ ( v4_relat_2 @ sk_A )
    | ~ ( v8_relat_2 @ sk_A )
    | ~ ( v1_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( v1_relat_2 @ sk_A )
      | ~ ( v8_relat_2 @ sk_A )
      | ~ ( v4_relat_2 @ sk_A )
      | ~ ( v6_relat_2 @ sk_A )
      | ( v2_wellord1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r1_relat_2 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('18',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d9_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ~ ( r1_relat_2 @ X7 @ ( k3_relat_1 @ X7 ) )
      | ( v1_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v1_relat_2 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_relat_2 @ sk_A )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r8_relat_2 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r8_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r8_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(d16_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ~ ( r8_relat_2 @ X2 @ ( k3_relat_1 @ X2 ) )
      | ( v8_relat_2 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v8_relat_2 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v8_relat_2 @ sk_A )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r4_relat_2 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r4_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r4_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(d12_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_2])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v4_relat_2 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v4_relat_2 @ sk_A )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X6 )
      | ( r6_relat_2 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r6_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r6_relat_2 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d14_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ( r6_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X1: $i] :
      ( ~ ( r6_relat_2 @ X1 @ ( k3_relat_1 @ X1 ) )
      | ( v6_relat_2 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_2])).

thf('49',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v6_relat_2 @ sk_A ) )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v6_relat_2 @ sk_A )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_wellord1 @ sk_A )
   <= ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','24','33','42','51'])).

thf('53',plain,
    ( ~ ( v2_wellord1 @ sk_A )
   <= ~ ( v2_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( v2_wellord1 @ sk_A )
    | ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_wellord1 @ sk_A )
    | ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('56',plain,
    ( ( v2_wellord1 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( v1_wellord1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('59',plain,
    ( ( v1_wellord1 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_wellord1 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X8: $i] :
      ( ~ ( v1_wellord1 @ X8 )
      | ( r1_wellord1 @ X8 @ ( k3_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord1])).

thf('62',plain,(
    ! [X1: $i] :
      ( ~ ( v6_relat_2 @ X1 )
      | ( r6_relat_2 @ X1 @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_2])).

thf('64',plain,(
    ! [X2: $i] :
      ( ~ ( v8_relat_2 @ X2 )
      | ( r8_relat_2 @ X2 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf('65',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_2 @ X7 )
      | ( r1_relat_2 @ X7 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_relat_2 @ X4 @ X5 )
      | ~ ( r8_relat_2 @ X4 @ X5 )
      | ~ ( r4_relat_2 @ X4 @ X5 )
      | ~ ( r6_relat_2 @ X4 @ X5 )
      | ~ ( r1_wellord1 @ X4 @ X5 )
      | ( r2_wellord1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_wellord1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r8_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r6_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_2 @ X0 )
      | ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_wellord1 @ sk_A )
      | ~ ( v6_relat_2 @ sk_A )
      | ~ ( v4_relat_2 @ sk_A )
      | ~ ( v8_relat_2 @ sk_A )
      | ~ ( v1_relat_2 @ sk_A ) )
   <= ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ~ ( v1_wellord1 @ sk_A )
      | ~ ( v6_relat_2 @ sk_A )
      | ~ ( v4_relat_2 @ sk_A )
      | ~ ( v8_relat_2 @ sk_A )
      | ~ ( v1_relat_2 @ sk_A ) )
   <= ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( v1_relat_2 @ sk_A )
      | ~ ( v8_relat_2 @ sk_A )
      | ~ ( v4_relat_2 @ sk_A )
      | ~ ( v6_relat_2 @ sk_A ) )
   <= ( ~ ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
      & ( v2_wellord1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','80'])).

thf('82',plain,
    ( ( v2_wellord1 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( v1_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('85',plain,
    ( ( v1_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_relat_2 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( v2_wellord1 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( v8_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('90',plain,
    ( ( v8_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v8_relat_2 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( v2_wellord1 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('93',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( v4_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('95',plain,
    ( ( v4_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v4_relat_2 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( v2_wellord1 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( v6_relat_2 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('100',plain,
    ( ( v6_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v6_relat_2 @ sk_A )
   <= ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( r2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','86','91','96','101'])).

thf('103',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','54','55','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ljZtpQymPZ
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:44:38 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 64 iterations in 0.028s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.22/0.51  thf(r6_relat_2_type, type, r6_relat_2: $i > $i > $o).
% 0.22/0.51  thf(r1_wellord1_type, type, r1_wellord1: $i > $i > $o).
% 0.22/0.51  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.22/0.51  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.22/0.51  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.22/0.51  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.22/0.51  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.22/0.51  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.22/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.51  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.22/0.51  thf(t8_wellord1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) ) <=> ( v2_wellord1 @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( v1_relat_1 @ A ) =>
% 0.22/0.51          ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) ) <=> ( v2_wellord1 @ A ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t8_wellord1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (v2_wellord1 @ sk_A) | ~ (r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (~ ((v2_wellord1 @ sk_A)) | 
% 0.22/0.51       ~ ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((v2_wellord1 @ sk_A) | (r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf(d5_wellord1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( r2_wellord1 @ A @ B ) <=>
% 0.22/0.51           ( ( r1_relat_2 @ A @ B ) & ( r8_relat_2 @ A @ B ) & 
% 0.22/0.51             ( r4_relat_2 @ A @ B ) & ( r6_relat_2 @ A @ B ) & 
% 0.22/0.51             ( r1_wellord1 @ A @ B ) ) ) ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X4 : $i, X6 : $i]:
% 0.22/0.51         (~ (r2_wellord1 @ X4 @ X6)
% 0.22/0.51          | (r1_wellord1 @ X4 @ X6)
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (r1_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((r1_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf(t5_wellord1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( v1_wellord1 @ A ) <=> ( r1_wellord1 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X8 : $i]:
% 0.22/0.51         (~ (r1_wellord1 @ X8 @ (k3_relat_1 @ X8))
% 0.22/0.51          | (v1_wellord1 @ X8)
% 0.22/0.51          | ~ (v1_relat_1 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t5_wellord1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (v1_wellord1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (((v1_wellord1 @ sk_A)) <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d4_wellord1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( v2_wellord1 @ A ) <=>
% 0.22/0.51         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.22/0.51           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v1_relat_2 @ X3)
% 0.22/0.51          | ~ (v8_relat_2 @ X3)
% 0.22/0.51          | ~ (v4_relat_2 @ X3)
% 0.22/0.51          | ~ (v6_relat_2 @ X3)
% 0.22/0.51          | ~ (v1_wellord1 @ X3)
% 0.22/0.51          | (v2_wellord1 @ X3)
% 0.22/0.51          | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (((v2_wellord1 @ sk_A)
% 0.22/0.51        | ~ (v1_wellord1 @ sk_A)
% 0.22/0.51        | ~ (v6_relat_2 @ sk_A)
% 0.22/0.51        | ~ (v4_relat_2 @ sk_A)
% 0.22/0.51        | ~ (v8_relat_2 @ sk_A)
% 0.22/0.51        | ~ (v1_relat_2 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (((~ (v1_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v8_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v4_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v6_relat_2 @ sk_A)
% 0.22/0.51         | (v2_wellord1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X4 : $i, X6 : $i]:
% 0.22/0.51         (~ (r2_wellord1 @ X4 @ X6)
% 0.22/0.51          | (r1_relat_2 @ X4 @ X6)
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (r1_relat_2 @ sk_A @ (k3_relat_1 @ sk_A))))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (((r1_relat_2 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf(d9_relat_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( v1_relat_2 @ A ) <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X7 : $i]:
% 0.22/0.51         (~ (r1_relat_2 @ X7 @ (k3_relat_1 @ X7))
% 0.22/0.51          | (v1_relat_2 @ X7)
% 0.22/0.51          | ~ (v1_relat_1 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (v1_relat_2 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (((v1_relat_2 @ sk_A)) <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X4 : $i, X6 : $i]:
% 0.22/0.51         (~ (r2_wellord1 @ X4 @ X6)
% 0.22/0.51          | (r8_relat_2 @ X4 @ X6)
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (r8_relat_2 @ sk_A @ (k3_relat_1 @ sk_A))))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (((r8_relat_2 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf(d16_relat_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( v8_relat_2 @ A ) <=> ( r8_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X2 : $i]:
% 0.22/0.51         (~ (r8_relat_2 @ X2 @ (k3_relat_1 @ X2))
% 0.22/0.51          | (v8_relat_2 @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d16_relat_2])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (v8_relat_2 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((v8_relat_2 @ sk_A)) <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X4 : $i, X6 : $i]:
% 0.22/0.51         (~ (r2_wellord1 @ X4 @ X6)
% 0.22/0.51          | (r4_relat_2 @ X4 @ X6)
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (r4_relat_2 @ sk_A @ (k3_relat_1 @ sk_A))))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (((r4_relat_2 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf(d12_relat_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( v4_relat_2 @ A ) <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [d12_relat_2])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (v4_relat_2 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (((v4_relat_2 @ sk_A)) <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X4 : $i, X6 : $i]:
% 0.22/0.51         (~ (r2_wellord1 @ X4 @ X6)
% 0.22/0.51          | (r6_relat_2 @ X4 @ X6)
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (r6_relat_2 @ sk_A @ (k3_relat_1 @ sk_A))))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.51  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (((r6_relat_2 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.51  thf(d14_relat_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( v6_relat_2 @ A ) <=> ( r6_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X1 : $i]:
% 0.22/0.51         (~ (r6_relat_2 @ X1 @ (k3_relat_1 @ X1))
% 0.22/0.51          | (v6_relat_2 @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d14_relat_2])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A) | (v6_relat_2 @ sk_A)))
% 0.22/0.51         <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.51  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (((v6_relat_2 @ sk_A)) <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (((v2_wellord1 @ sk_A)) <= (((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '24', '33', '42', '51'])).
% 0.22/0.51  thf('53', plain, ((~ (v2_wellord1 @ sk_A)) <= (~ ((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (((v2_wellord1 @ sk_A)) | ~ ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (((v2_wellord1 @ sk_A)) | ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('56', plain, (((v2_wellord1 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_wellord1 @ X3) | (v1_wellord1 @ X3) | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.51  thf('59', plain, (((v1_wellord1 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.51  thf('60', plain, (((v1_wellord1 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['56', '59'])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      (![X8 : $i]:
% 0.22/0.51         (~ (v1_wellord1 @ X8)
% 0.22/0.51          | (r1_wellord1 @ X8 @ (k3_relat_1 @ X8))
% 0.22/0.51          | ~ (v1_relat_1 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t5_wellord1])).
% 0.22/0.51  thf('62', plain,
% 0.22/0.51      (![X1 : $i]:
% 0.22/0.51         (~ (v6_relat_2 @ X1)
% 0.22/0.51          | (r6_relat_2 @ X1 @ (k3_relat_1 @ X1))
% 0.22/0.51          | ~ (v1_relat_1 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d14_relat_2])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v4_relat_2 @ X0)
% 0.22/0.51          | (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [d12_relat_2])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      (![X2 : $i]:
% 0.22/0.51         (~ (v8_relat_2 @ X2)
% 0.22/0.51          | (r8_relat_2 @ X2 @ (k3_relat_1 @ X2))
% 0.22/0.51          | ~ (v1_relat_1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d16_relat_2])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (![X7 : $i]:
% 0.22/0.51         (~ (v1_relat_2 @ X7)
% 0.22/0.51          | (r1_relat_2 @ X7 @ (k3_relat_1 @ X7))
% 0.22/0.51          | ~ (v1_relat_1 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.22/0.51  thf('66', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r1_relat_2 @ X4 @ X5)
% 0.22/0.51          | ~ (r8_relat_2 @ X4 @ X5)
% 0.22/0.51          | ~ (r4_relat_2 @ X4 @ X5)
% 0.22/0.51          | ~ (r6_relat_2 @ X4 @ X5)
% 0.22/0.51          | ~ (r1_wellord1 @ X4 @ X5)
% 0.22/0.51          | (r2_wellord1 @ X4 @ X5)
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_wellord1])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r8_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r8_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['67'])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['64', '68'])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['69'])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['63', '70'])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r6_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['71'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v6_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['62', '72'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v6_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['73'])).
% 0.22/0.51  thf('75', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_wellord1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v6_relat_2 @ X0)
% 0.22/0.51          | ~ (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | (r2_wellord1 @ X0 @ (k3_relat_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['61', '74'])).
% 0.22/0.51  thf('76', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_2 @ X0)
% 0.22/0.51          | ~ (v8_relat_2 @ X0)
% 0.22/0.51          | ~ (v4_relat_2 @ X0)
% 0.22/0.51          | ~ (v6_relat_2 @ X0)
% 0.22/0.51          | ~ (v1_wellord1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['75'])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      ((~ (r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))
% 0.22/0.51         <= (~ ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A)
% 0.22/0.51         | ~ (v1_wellord1 @ sk_A)
% 0.22/0.51         | ~ (v6_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v4_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v8_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v1_relat_2 @ sk_A)))
% 0.22/0.51         <= (~ ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.51  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      (((~ (v1_wellord1 @ sk_A)
% 0.22/0.51         | ~ (v6_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v4_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v8_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v1_relat_2 @ sk_A)))
% 0.22/0.51         <= (~ ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      (((~ (v1_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v8_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v4_relat_2 @ sk_A)
% 0.22/0.51         | ~ (v6_relat_2 @ sk_A)))
% 0.22/0.51         <= (~ ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A))) & 
% 0.22/0.51             ((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['60', '80'])).
% 0.22/0.51  thf('82', plain, (((v2_wellord1 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('84', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_wellord1 @ X3) | (v1_relat_2 @ X3) | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.51  thf('85', plain, (((v1_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.51  thf('86', plain, (((v1_relat_2 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['82', '85'])).
% 0.22/0.51  thf('87', plain, (((v2_wellord1 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('89', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_wellord1 @ X3) | (v8_relat_2 @ X3) | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.51  thf('90', plain, (((v8_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.51  thf('91', plain, (((v8_relat_2 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['87', '90'])).
% 0.22/0.51  thf('92', plain, (((v2_wellord1 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('93', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('94', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_wellord1 @ X3) | (v4_relat_2 @ X3) | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.51  thf('95', plain, (((v4_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.51  thf('96', plain, (((v4_relat_2 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['92', '95'])).
% 0.22/0.51  thf('97', plain, (((v2_wellord1 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_wellord1 @ X3) | (v6_relat_2 @ X3) | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.22/0.51  thf('100', plain, (((v6_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['98', '99'])).
% 0.22/0.51  thf('101', plain, (((v6_relat_2 @ sk_A)) <= (((v2_wellord1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['97', '100'])).
% 0.22/0.51  thf('102', plain,
% 0.22/0.51      (~ ((v2_wellord1 @ sk_A)) | ((r2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['81', '86', '91', '96', '101'])).
% 0.22/0.51  thf('103', plain, ($false),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['1', '54', '55', '102'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
