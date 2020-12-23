%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ultwJmSo3g

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 741 expanded)
%              Number of leaves         :   26 ( 230 expanded)
%              Depth                    :   32
%              Number of atoms          :  938 (7464 expanded)
%              Number of equality atoms :   60 ( 548 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(t50_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_xboole_0 @ A @ B )
              & ( A != B )
              & ~ ( r2_xboole_0 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r2_xboole_0 @ X6 @ X5 )
      | ( X6 = X5 )
      | ( r2_xboole_0 @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t50_ordinal1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X20 ) )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('9',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X22 ) @ X21 )
        = ( k1_wellord2 @ X21 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ( X19
        = ( k1_wellord1 @ ( k1_wellord2 @ X18 ) @ X19 ) )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ~ ( r4_wellord1 @ X11 @ ( k2_wellord1 @ X11 @ ( k1_wellord1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
       != ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('21',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
        = X13 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('46',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X20: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X20 ) )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ( X19
        = ( k1_wellord1 @ ( k1_wellord2 @ X18 ) @ X19 ) )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('57',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X11 )
      | ~ ( r4_wellord1 @ X11 @ ( k2_wellord1 @ X11 @ ( k1_wellord1 @ X11 @ X12 ) ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('65',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
      = sk_B )
    | ( r2_xboole_0 @ sk_B @ ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r4_wellord1 @ X9 @ X10 )
      | ~ ( r4_wellord1 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('72',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('73',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('75',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('77',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('78',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('79',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','73','74','75','76','77','78','79'])).

thf('81',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','82'])).

thf('84',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('87',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['53','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ultwJmSo3g
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 97 iterations in 0.059s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.51  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.51  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.51  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.21/0.51  thf(t50_ordinal1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.51           ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.51                ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X5)
% 0.21/0.51          | (r2_xboole_0 @ X6 @ X5)
% 0.21/0.51          | ((X6) = (X5))
% 0.21/0.51          | (r2_xboole_0 @ X5 @ X6)
% 0.21/0.51          | ~ (v3_ordinal1 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t50_ordinal1])).
% 0.21/0.51  thf(d8_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | (r1_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(t24_ordinal1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.51           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.51                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X3)
% 0.21/0.51          | (r2_hidden @ X4 @ X3)
% 0.21/0.51          | ((X4) = (X3))
% 0.21/0.51          | (r2_hidden @ X3 @ X4)
% 0.21/0.51          | ~ (v3_ordinal1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.21/0.51  thf(t7_ordinal1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (r2_hidden @ X1 @ X0)
% 0.21/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ X1 @ X0)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf(t7_wellord2, axiom,
% 0.21/0.51    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X20 : $i]:
% 0.21/0.51         ((v2_wellord1 @ (k1_wellord2 @ X20)) | ~ (v3_ordinal1 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.21/0.51  thf(t11_wellord2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.51           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.21/0.51             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.51              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.21/0.51                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | (r1_tarski @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(t8_wellord2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i]:
% 0.21/0.51         (((k2_wellord1 @ (k1_wellord2 @ X22) @ X21) = (k1_wellord2 @ X21))
% 0.21/0.51          | ~ (r1_tarski @ X21 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ X1 @ X0)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.51  thf(t10_wellord2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.51           ( ( r2_hidden @ A @ B ) =>
% 0.21/0.51             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X18)
% 0.21/0.51          | ((X19) = (k1_wellord1 @ (k1_wellord2 @ X18) @ X19))
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X18)
% 0.21/0.51          | ~ (v3_ordinal1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf(t57_wellord1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( v2_wellord1 @ A ) =>
% 0.21/0.51         ( ![B:$i]:
% 0.21/0.51           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.21/0.51                ( r4_wellord1 @
% 0.21/0.51                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v2_wellord1 @ X11)
% 0.21/0.51          | ~ (r4_wellord1 @ X11 @ 
% 0.21/0.51               (k2_wellord1 @ X11 @ (k1_wellord1 @ X11 @ X12)))
% 0.21/0.51          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X11))
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.21/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.51  thf('19', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.51  thf(d1_wellord2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.51         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.51           ( ![C:$i,D:$i]:
% 0.21/0.51             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.51                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (((X14) != (k1_wellord2 @ X13))
% 0.21/0.51          | ((k3_relat_1 @ X14) = (X13))
% 0.21/0.51          | ~ (v1_relat_1 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X13 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ X13))
% 0.21/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.51  thf('22', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.51  thf('23', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((~ (v3_ordinal1 @ sk_B)
% 0.21/0.51        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51        | ((sk_B) = (sk_A))
% 0.21/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.21/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.51        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '26'])).
% 0.21/0.51  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51        | ((sk_B) = (sk_A))
% 0.21/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.51        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.51  thf('31', plain, (((sk_A) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.51        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.51        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '32'])).
% 0.21/0.51  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_B @ sk_A) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.51        | ((sk_B) = (sk_A))
% 0.21/0.51        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.21/0.51        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '35'])).
% 0.21/0.51  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((((sk_B) = (sk_A))
% 0.21/0.51        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.51  thf('40', plain, (((r2_xboole_0 @ sk_A @ sk_B) | ((sk_B) = (sk_A)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.51  thf('41', plain, (((sk_A) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.51  thf('44', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | ~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.51        | ((sk_B) = (sk_A))
% 0.21/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('49', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.51  thf('50', plain, (((sk_A) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.51  thf('53', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X20 : $i]:
% 0.21/0.51         ((v2_wellord1 @ (k1_wellord2 @ X20)) | ~ (v3_ordinal1 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.21/0.51  thf('55', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X18)
% 0.21/0.51          | ((X19) = (k1_wellord1 @ (k1_wellord2 @ X18) @ X19))
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X18)
% 0.21/0.51          | ~ (v3_ordinal1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.51        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.21/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_ordinal1 @ X0)
% 0.21/0.51          | ((X1) = (X0))
% 0.21/0.51          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v2_wellord1 @ X11)
% 0.21/0.51          | ~ (r4_wellord1 @ X11 @ 
% 0.21/0.51               (k2_wellord1 @ X11 @ (k1_wellord1 @ X11 @ X12)))
% 0.21/0.51          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X11))
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.51             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.51          | ~ (v3_ordinal1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.51          | (r2_xboole_0 @ X1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.51          | ((k1_wellord1 @ (k1_wellord2 @ X1) @ X0) = (X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.21/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.51  thf('65', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.51             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.51          | ~ (v3_ordinal1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.51          | (r2_xboole_0 @ X1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.51          | ((k1_wellord1 @ (k1_wellord2 @ X1) @ X0) = (X1))
% 0.21/0.51          | ~ (v3_ordinal1 @ X1)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.21/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.21/0.51        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.21/0.51        | ((k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (sk_B))
% 0.21/0.51        | (r2_xboole_0 @ sk_B @ (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.21/0.51        | ~ (v3_ordinal1 @ (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['60', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t50_wellord1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X9)
% 0.21/0.51          | (r4_wellord1 @ X9 @ X10)
% 0.21/0.51          | ~ (r4_wellord1 @ X10 @ X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.21/0.51        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.21/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.51  thf('72', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.21/0.51  thf('74', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('75', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('76', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.51  thf('77', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.51  thf('78', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.51  thf('79', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.21/0.51        | ((sk_A) = (sk_B))
% 0.21/0.51        | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['67', '73', '74', '75', '76', '77', '78', '79'])).
% 0.21/0.51  thf('81', plain, (((sk_A) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B)) | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.21/0.51  thf('83', plain, ((~ (v3_ordinal1 @ sk_B) | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '82'])).
% 0.21/0.51  thf('84', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('85', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.51  thf('87', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.51  thf('88', plain, ($false), inference('demod', [status(thm)], ['53', '87'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
