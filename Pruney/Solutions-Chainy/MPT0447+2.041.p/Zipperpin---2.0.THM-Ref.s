%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0NnjfQyHyf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:58 EST 2020

% Result     : Theorem 9.51s
% Output     : Refutation 9.51s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 195 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  620 (1470 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X52: $i] :
      ( ( ( k3_relat_1 @ X52 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X52: $i] :
      ( ( ( k3_relat_1 @ X52 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_xboole_0 @ X27 @ X29 )
      | ( ( k4_xboole_0 @ X27 @ X29 )
       != X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( k2_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k1_relat_1 @ X56 ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( r1_tarski @ X56 @ X55 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X52: $i] :
      ( ( ( k3_relat_1 @ X52 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( k2_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( r1_tarski @ ( k2_relat_1 @ X56 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( r1_tarski @ X56 @ X55 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('52',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ( r1_tarski @ ( k2_xboole_0 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_2 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('57',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ( r1_tarski @ ( k2_xboole_0 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['54','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0NnjfQyHyf
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.51/9.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.51/9.76  % Solved by: fo/fo7.sh
% 9.51/9.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.51/9.76  % done 14574 iterations in 9.300s
% 9.51/9.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.51/9.76  % SZS output start Refutation
% 9.51/9.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.51/9.76  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 9.51/9.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.51/9.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.51/9.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.51/9.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.51/9.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.51/9.76  thf(sk_B_2_type, type, sk_B_2: $i).
% 9.51/9.76  thf(sk_A_type, type, sk_A: $i).
% 9.51/9.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.51/9.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.51/9.76  thf(t31_relat_1, conjecture,
% 9.51/9.76    (![A:$i]:
% 9.51/9.76     ( ( v1_relat_1 @ A ) =>
% 9.51/9.76       ( ![B:$i]:
% 9.51/9.76         ( ( v1_relat_1 @ B ) =>
% 9.51/9.76           ( ( r1_tarski @ A @ B ) =>
% 9.51/9.76             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 9.51/9.76  thf(zf_stmt_0, negated_conjecture,
% 9.51/9.76    (~( ![A:$i]:
% 9.51/9.76        ( ( v1_relat_1 @ A ) =>
% 9.51/9.76          ( ![B:$i]:
% 9.51/9.76            ( ( v1_relat_1 @ B ) =>
% 9.51/9.76              ( ( r1_tarski @ A @ B ) =>
% 9.51/9.76                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 9.51/9.76    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 9.51/9.76  thf('0', plain,
% 9.51/9.76      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf(d6_relat_1, axiom,
% 9.51/9.76    (![A:$i]:
% 9.51/9.76     ( ( v1_relat_1 @ A ) =>
% 9.51/9.76       ( ( k3_relat_1 @ A ) =
% 9.51/9.76         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 9.51/9.76  thf('1', plain,
% 9.51/9.76      (![X52 : $i]:
% 9.51/9.76         (((k3_relat_1 @ X52)
% 9.51/9.76            = (k2_xboole_0 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52)))
% 9.51/9.76          | ~ (v1_relat_1 @ X52))),
% 9.51/9.76      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.51/9.76  thf('2', plain,
% 9.51/9.76      (![X52 : $i]:
% 9.51/9.76         (((k3_relat_1 @ X52)
% 9.51/9.76            = (k2_xboole_0 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52)))
% 9.51/9.76          | ~ (v1_relat_1 @ X52))),
% 9.51/9.76      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.51/9.76  thf(idempotence_k2_xboole_0, axiom,
% 9.51/9.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 9.51/9.76  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 9.51/9.76      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 9.51/9.76  thf(t41_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i,C:$i]:
% 9.51/9.76     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.51/9.76       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.51/9.76  thf('4', plain,
% 9.51/9.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.51/9.76         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 9.51/9.76           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 9.51/9.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.51/9.76  thf(t83_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i]:
% 9.51/9.76     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.51/9.76  thf('5', plain,
% 9.51/9.76      (![X27 : $i, X29 : $i]:
% 9.51/9.76         ((r1_xboole_0 @ X27 @ X29) | ((k4_xboole_0 @ X27 @ X29) != (X27)))),
% 9.51/9.76      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.51/9.76  thf('6', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.76         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 9.51/9.76            != (k4_xboole_0 @ X2 @ X1))
% 9.51/9.76          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['4', '5'])).
% 9.51/9.76  thf('7', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]:
% 9.51/9.76         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 9.51/9.76          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['3', '6'])).
% 9.51/9.76  thf('8', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 9.51/9.76      inference('simplify', [status(thm)], ['7'])).
% 9.51/9.76  thf(t36_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.51/9.76  thf('9', plain,
% 9.51/9.76      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 9.51/9.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.51/9.76  thf(t10_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i,C:$i]:
% 9.51/9.76     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 9.51/9.76  thf('10', plain,
% 9.51/9.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 9.51/9.76         (~ (r1_tarski @ X9 @ X10)
% 9.51/9.76          | (r1_tarski @ X9 @ (k2_xboole_0 @ X11 @ X10)))),
% 9.51/9.76      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.51/9.76  thf('11', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.76         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['9', '10'])).
% 9.51/9.76  thf(t73_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i,C:$i]:
% 9.51/9.76     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 9.51/9.76       ( r1_tarski @ A @ B ) ))).
% 9.51/9.76  thf('12', plain,
% 9.51/9.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.51/9.76         ((r1_tarski @ X24 @ X25)
% 9.51/9.76          | ~ (r1_tarski @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 9.51/9.76          | ~ (r1_xboole_0 @ X24 @ X26))),
% 9.51/9.76      inference('cnf', [status(esa)], [t73_xboole_1])).
% 9.51/9.76  thf('13', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.76         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X0)
% 9.51/9.76          | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 9.51/9.76      inference('sup-', [status(thm)], ['11', '12'])).
% 9.51/9.76  thf('14', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 9.51/9.76      inference('sup-', [status(thm)], ['8', '13'])).
% 9.51/9.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.51/9.76  thf('15', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 9.51/9.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.51/9.76  thf(d10_xboole_0, axiom,
% 9.51/9.76    (![A:$i,B:$i]:
% 9.51/9.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.51/9.76  thf('16', plain,
% 9.51/9.76      (![X6 : $i, X8 : $i]:
% 9.51/9.76         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 9.51/9.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.51/9.76  thf('17', plain,
% 9.51/9.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['15', '16'])).
% 9.51/9.76  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['14', '17'])).
% 9.51/9.76  thf(t44_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i,C:$i]:
% 9.51/9.76     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 9.51/9.76       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.51/9.76  thf('19', plain,
% 9.51/9.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.51/9.76         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 9.51/9.76          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 9.51/9.76      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.51/9.76  thf('20', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]:
% 9.51/9.76         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 9.51/9.76          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['18', '19'])).
% 9.51/9.76  thf('21', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 9.51/9.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.51/9.76  thf('22', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.51/9.76      inference('demod', [status(thm)], ['20', '21'])).
% 9.51/9.76  thf('23', plain,
% 9.51/9.76      (![X0 : $i]:
% 9.51/9.76         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 9.51/9.76          | ~ (v1_relat_1 @ X0))),
% 9.51/9.76      inference('sup+', [status(thm)], ['2', '22'])).
% 9.51/9.76  thf('24', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf(t25_relat_1, axiom,
% 9.51/9.76    (![A:$i]:
% 9.51/9.76     ( ( v1_relat_1 @ A ) =>
% 9.51/9.76       ( ![B:$i]:
% 9.51/9.76         ( ( v1_relat_1 @ B ) =>
% 9.51/9.76           ( ( r1_tarski @ A @ B ) =>
% 9.51/9.76             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 9.51/9.76               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 9.51/9.76  thf('25', plain,
% 9.51/9.76      (![X55 : $i, X56 : $i]:
% 9.51/9.76         (~ (v1_relat_1 @ X55)
% 9.51/9.76          | (r1_tarski @ (k1_relat_1 @ X56) @ (k1_relat_1 @ X55))
% 9.51/9.76          | ~ (r1_tarski @ X56 @ X55)
% 9.51/9.76          | ~ (v1_relat_1 @ X56))),
% 9.51/9.76      inference('cnf', [status(esa)], [t25_relat_1])).
% 9.51/9.76  thf('26', plain,
% 9.51/9.76      ((~ (v1_relat_1 @ sk_A)
% 9.51/9.76        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))
% 9.51/9.76        | ~ (v1_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('sup-', [status(thm)], ['24', '25'])).
% 9.51/9.76  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('28', plain, ((v1_relat_1 @ sk_B_2)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('demod', [status(thm)], ['26', '27', '28'])).
% 9.51/9.76  thf(t1_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i,C:$i]:
% 9.51/9.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 9.51/9.76       ( r1_tarski @ A @ C ) ))).
% 9.51/9.76  thf('30', plain,
% 9.51/9.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.76         (~ (r1_tarski @ X12 @ X13)
% 9.51/9.76          | ~ (r1_tarski @ X13 @ X14)
% 9.51/9.76          | (r1_tarski @ X12 @ X14))),
% 9.51/9.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.51/9.76  thf('31', plain,
% 9.51/9.76      (![X0 : $i]:
% 9.51/9.76         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 9.51/9.76          | ~ (r1_tarski @ (k1_relat_1 @ sk_B_2) @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['29', '30'])).
% 9.51/9.76  thf('32', plain,
% 9.51/9.76      ((~ (v1_relat_1 @ sk_B_2)
% 9.51/9.76        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['23', '31'])).
% 9.51/9.76  thf('33', plain, ((v1_relat_1 @ sk_B_2)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('34', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('demod', [status(thm)], ['32', '33'])).
% 9.51/9.76  thf('35', plain,
% 9.51/9.76      (![X52 : $i]:
% 9.51/9.76         (((k3_relat_1 @ X52)
% 9.51/9.76            = (k2_xboole_0 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52)))
% 9.51/9.76          | ~ (v1_relat_1 @ X52))),
% 9.51/9.76      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.51/9.76  thf('36', plain,
% 9.51/9.76      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 9.51/9.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.51/9.76  thf('37', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 9.51/9.76      inference('simplify', [status(thm)], ['36'])).
% 9.51/9.76  thf('38', plain,
% 9.51/9.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 9.51/9.76         (~ (r1_tarski @ X9 @ X10)
% 9.51/9.76          | (r1_tarski @ X9 @ (k2_xboole_0 @ X11 @ X10)))),
% 9.51/9.76      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.51/9.76  thf('39', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['37', '38'])).
% 9.51/9.76  thf('40', plain,
% 9.51/9.76      (![X0 : $i]:
% 9.51/9.76         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 9.51/9.76          | ~ (v1_relat_1 @ X0))),
% 9.51/9.76      inference('sup+', [status(thm)], ['35', '39'])).
% 9.51/9.76  thf('41', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('42', plain,
% 9.51/9.76      (![X55 : $i, X56 : $i]:
% 9.51/9.76         (~ (v1_relat_1 @ X55)
% 9.51/9.76          | (r1_tarski @ (k2_relat_1 @ X56) @ (k2_relat_1 @ X55))
% 9.51/9.76          | ~ (r1_tarski @ X56 @ X55)
% 9.51/9.76          | ~ (v1_relat_1 @ X56))),
% 9.51/9.76      inference('cnf', [status(esa)], [t25_relat_1])).
% 9.51/9.76  thf('43', plain,
% 9.51/9.76      ((~ (v1_relat_1 @ sk_A)
% 9.51/9.76        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))
% 9.51/9.76        | ~ (v1_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('sup-', [status(thm)], ['41', '42'])).
% 9.51/9.76  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('45', plain, ((v1_relat_1 @ sk_B_2)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('46', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('demod', [status(thm)], ['43', '44', '45'])).
% 9.51/9.76  thf('47', plain,
% 9.51/9.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.51/9.76         (~ (r1_tarski @ X12 @ X13)
% 9.51/9.76          | ~ (r1_tarski @ X13 @ X14)
% 9.51/9.76          | (r1_tarski @ X12 @ X14))),
% 9.51/9.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.51/9.76  thf('48', plain,
% 9.51/9.76      (![X0 : $i]:
% 9.51/9.76         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 9.51/9.76          | ~ (r1_tarski @ (k2_relat_1 @ sk_B_2) @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['46', '47'])).
% 9.51/9.76  thf('49', plain,
% 9.51/9.76      ((~ (v1_relat_1 @ sk_B_2)
% 9.51/9.76        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['40', '48'])).
% 9.51/9.76  thf('50', plain, ((v1_relat_1 @ sk_B_2)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('51', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('demod', [status(thm)], ['49', '50'])).
% 9.51/9.76  thf(t8_xboole_1, axiom,
% 9.51/9.76    (![A:$i,B:$i,C:$i]:
% 9.51/9.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 9.51/9.76       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 9.51/9.76  thf('52', plain,
% 9.51/9.76      (![X30 : $i, X31 : $i, X32 : $i]:
% 9.51/9.76         (~ (r1_tarski @ X30 @ X31)
% 9.51/9.76          | ~ (r1_tarski @ X32 @ X31)
% 9.51/9.76          | (r1_tarski @ (k2_xboole_0 @ X30 @ X32) @ X31))),
% 9.51/9.76      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.51/9.76  thf('53', plain,
% 9.51/9.76      (![X0 : $i]:
% 9.51/9.76         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 9.51/9.76           (k3_relat_1 @ sk_B_2))
% 9.51/9.76          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_2)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['51', '52'])).
% 9.51/9.76  thf('54', plain,
% 9.51/9.76      ((r1_tarski @ 
% 9.51/9.76        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 9.51/9.76        (k3_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('sup-', [status(thm)], ['34', '53'])).
% 9.51/9.76  thf('55', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.51/9.76      inference('demod', [status(thm)], ['20', '21'])).
% 9.51/9.76  thf('56', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['37', '38'])).
% 9.51/9.76  thf('57', plain,
% 9.51/9.76      (![X30 : $i, X31 : $i, X32 : $i]:
% 9.51/9.76         (~ (r1_tarski @ X30 @ X31)
% 9.51/9.76          | ~ (r1_tarski @ X32 @ X31)
% 9.51/9.76          | (r1_tarski @ (k2_xboole_0 @ X30 @ X32) @ X31))),
% 9.51/9.76      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.51/9.76  thf('58', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.76         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 9.51/9.76          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['56', '57'])).
% 9.51/9.76  thf('59', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]:
% 9.51/9.76         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['55', '58'])).
% 9.51/9.76  thf('60', plain,
% 9.51/9.76      (![X6 : $i, X8 : $i]:
% 9.51/9.76         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 9.51/9.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.51/9.76  thf('61', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]:
% 9.51/9.76         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 9.51/9.76          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 9.51/9.76      inference('sup-', [status(thm)], ['59', '60'])).
% 9.51/9.76  thf('62', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]:
% 9.51/9.76         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 9.51/9.76      inference('sup-', [status(thm)], ['55', '58'])).
% 9.51/9.76  thf('63', plain,
% 9.51/9.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.51/9.76      inference('demod', [status(thm)], ['61', '62'])).
% 9.51/9.76  thf('64', plain,
% 9.51/9.76      ((r1_tarski @ 
% 9.51/9.76        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 9.51/9.76        (k3_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('demod', [status(thm)], ['54', '63'])).
% 9.51/9.76  thf('65', plain,
% 9.51/9.76      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))
% 9.51/9.76        | ~ (v1_relat_1 @ sk_A))),
% 9.51/9.76      inference('sup+', [status(thm)], ['1', '64'])).
% 9.51/9.76  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 9.51/9.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.76  thf('67', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.51/9.76      inference('demod', [status(thm)], ['65', '66'])).
% 9.51/9.76  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 9.51/9.76  
% 9.51/9.76  % SZS output end Refutation
% 9.51/9.76  
% 9.51/9.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
