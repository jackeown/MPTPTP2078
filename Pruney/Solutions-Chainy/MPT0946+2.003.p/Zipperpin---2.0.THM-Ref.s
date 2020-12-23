%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NuB4XyZOes

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 466 expanded)
%              Number of leaves         :   26 ( 153 expanded)
%              Depth                    :   33
%              Number of atoms          : 1182 (4451 expanded)
%              Number of equality atoms :   70 ( 289 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ( r2_hidden @ X7 @ X6 )
      | ( X7 = X6 )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ( r2_hidden @ X7 @ X6 )
      | ( X7 = X6 )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X19: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
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

thf('7',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r4_wellord1 @ X8 @ X9 )
      | ~ ( r4_wellord1 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X21 ) @ X20 )
        = ( k1_wellord2 @ X20 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( X18
        = ( k1_wellord1 @ ( k1_wellord2 @ X17 ) @ X18 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r4_wellord1 @ X10 @ ( k2_wellord1 @ X10 @ ( k1_wellord1 @ X10 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
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

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13
       != ( k1_wellord2 @ X12 ) )
      | ( ( k3_relat_1 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('26',plain,(
    ! [X12: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X12 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_ordinal1 @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('35',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('40',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','35','36','37','40'])).

thf('42',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','46'])).

thf('48',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X21 ) @ X20 )
        = ( k1_wellord2 @ X20 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('56',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B_1 )
    = ( k1_wellord2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ( r2_hidden @ X7 @ X6 )
      | ( X7 = X6 )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( X18
        = ( k1_wellord1 @ ( k1_wellord2 @ X17 ) @ X18 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r4_wellord1 @ X10 @ ( k2_wellord1 @ X10 @ ( k1_wellord1 @ X10 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( X18
        = ( k1_wellord1 @ ( k1_wellord2 @ X17 ) @ X18 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('84',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r4_wellord1 @ X10 @ ( k2_wellord1 @ X10 @ ( k1_wellord1 @ X10 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('89',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B_1 ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('91',plain,(
    ! [X19: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('92',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('94',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( v1_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('96',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('99',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','101'])).

thf('103',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( v1_ordinal1 @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','104'])).

thf('106',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('107',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( sk_A = sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X21 ) @ X20 )
        = ( k1_wellord2 @ X20 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('114',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_1 ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('116',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('117',plain,(
    ! [X12: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('118',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('119',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['89','114','115','116','117','118'])).

thf('120',plain,(
    ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','119'])).

thf('121',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['120','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NuB4XyZOes
% 0.09/0.31  % Computer   : n016.cluster.edu
% 0.09/0.31  % Model      : x86_64 x86_64
% 0.09/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.31  % Memory     : 8042.1875MB
% 0.09/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.31  % CPULimit   : 60
% 0.09/0.31  % DateTime   : Tue Dec  1 19:22:34 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.09/0.31  % Running portfolio for 600 s
% 0.09/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.31  % Number of cores: 8
% 0.16/0.32  % Python version: Python 3.6.8
% 0.16/0.32  % Running in FO mode
% 0.16/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.16/0.48  % Solved by: fo/fo7.sh
% 0.16/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.48  % done 69 iterations in 0.048s
% 0.16/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.16/0.48  % SZS output start Refutation
% 0.16/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.16/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.16/0.48  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.16/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.16/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.16/0.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.16/0.48  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.16/0.48  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.16/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.16/0.48  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.16/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.16/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.48  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.16/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.16/0.48  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.16/0.48  thf(t7_wellord2, axiom,
% 0.16/0.48    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.16/0.48  thf('0', plain,
% 0.16/0.48      (![X19 : $i]:
% 0.16/0.48         ((v2_wellord1 @ (k1_wellord2 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.16/0.48      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.16/0.48  thf(t24_ordinal1, axiom,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.16/0.48       ( ![B:$i]:
% 0.16/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.16/0.48           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.16/0.48                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.16/0.48  thf('1', plain,
% 0.16/0.48      (![X6 : $i, X7 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X6)
% 0.16/0.48          | (r2_hidden @ X7 @ X6)
% 0.16/0.48          | ((X7) = (X6))
% 0.16/0.48          | (r2_hidden @ X6 @ X7)
% 0.16/0.48          | ~ (v3_ordinal1 @ X7))),
% 0.16/0.48      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.16/0.48  thf('2', plain,
% 0.16/0.48      (![X19 : $i]:
% 0.16/0.48         ((v2_wellord1 @ (k1_wellord2 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.16/0.48      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.16/0.48  thf('3', plain,
% 0.16/0.48      (![X6 : $i, X7 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X6)
% 0.16/0.48          | (r2_hidden @ X7 @ X6)
% 0.16/0.48          | ((X7) = (X6))
% 0.16/0.48          | (r2_hidden @ X6 @ X7)
% 0.16/0.48          | ~ (v3_ordinal1 @ X7))),
% 0.16/0.48      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.16/0.48  thf(d2_ordinal1, axiom,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v1_ordinal1 @ A ) <=>
% 0.16/0.48       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.16/0.48  thf('4', plain,
% 0.16/0.48      (![X1 : $i, X2 : $i]:
% 0.16/0.48         (~ (r2_hidden @ X1 @ X2)
% 0.16/0.48          | (r1_tarski @ X1 @ X2)
% 0.16/0.48          | ~ (v1_ordinal1 @ X2))),
% 0.16/0.48      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.16/0.48  thf('5', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X1)
% 0.16/0.48          | (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.16/0.48  thf('6', plain,
% 0.16/0.48      (![X19 : $i]:
% 0.16/0.48         ((v2_wellord1 @ (k1_wellord2 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.16/0.48      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.16/0.48  thf(t11_wellord2, conjecture,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.16/0.48       ( ![B:$i]:
% 0.16/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.16/0.48           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.16/0.48             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.16/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.48    (~( ![A:$i]:
% 0.16/0.48        ( ( v3_ordinal1 @ A ) =>
% 0.16/0.48          ( ![B:$i]:
% 0.16/0.48            ( ( v3_ordinal1 @ B ) =>
% 0.16/0.48              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.16/0.48                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.16/0.48    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.16/0.48  thf('7', plain,
% 0.16/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf(t50_wellord1, axiom,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v1_relat_1 @ A ) =>
% 0.16/0.48       ( ![B:$i]:
% 0.16/0.48         ( ( v1_relat_1 @ B ) =>
% 0.16/0.48           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.16/0.48  thf('8', plain,
% 0.16/0.48      (![X8 : $i, X9 : $i]:
% 0.16/0.48         (~ (v1_relat_1 @ X8)
% 0.16/0.48          | (r4_wellord1 @ X8 @ X9)
% 0.16/0.48          | ~ (r4_wellord1 @ X9 @ X8)
% 0.16/0.48          | ~ (v1_relat_1 @ X9))),
% 0.16/0.48      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.16/0.48  thf('9', plain,
% 0.16/0.48      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B_1)))),
% 0.16/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.16/0.48  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.16/0.48  thf('10', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.16/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.16/0.48  thf('11', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.16/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.16/0.48  thf('12', plain,
% 0.16/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.16/0.48  thf('13', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X1)
% 0.16/0.48          | (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.16/0.48  thf('14', plain,
% 0.16/0.48      (![X1 : $i, X2 : $i]:
% 0.16/0.48         (~ (r2_hidden @ X1 @ X2)
% 0.16/0.48          | (r1_tarski @ X1 @ X2)
% 0.16/0.48          | ~ (v1_ordinal1 @ X2))),
% 0.16/0.48      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.16/0.48  thf('15', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         ((r1_tarski @ X0 @ X1)
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.16/0.48  thf(t8_wellord2, axiom,
% 0.16/0.48    (![A:$i,B:$i]:
% 0.16/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.16/0.48       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.16/0.48  thf('16', plain,
% 0.16/0.48      (![X20 : $i, X21 : $i]:
% 0.16/0.48         (((k2_wellord1 @ (k1_wellord2 @ X21) @ X20) = (k1_wellord2 @ X20))
% 0.16/0.48          | ~ (r1_tarski @ X20 @ X21))),
% 0.16/0.48      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.16/0.48  thf('17', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         ((r1_tarski @ X0 @ X1)
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.16/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.16/0.48  thf('18', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X1)
% 0.16/0.48          | (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.16/0.48  thf(t10_wellord2, axiom,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.16/0.48       ( ![B:$i]:
% 0.16/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.16/0.48           ( ( r2_hidden @ A @ B ) =>
% 0.16/0.48             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.16/0.48  thf('19', plain,
% 0.16/0.48      (![X17 : $i, X18 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X17)
% 0.16/0.48          | ((X18) = (k1_wellord1 @ (k1_wellord2 @ X17) @ X18))
% 0.16/0.48          | ~ (r2_hidden @ X18 @ X17)
% 0.16/0.48          | ~ (v3_ordinal1 @ X18))),
% 0.16/0.48      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.16/0.48  thf('20', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         ((r1_tarski @ X0 @ X1)
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.16/0.48  thf('21', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | (r1_tarski @ X0 @ X1))),
% 0.16/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.16/0.48  thf(t57_wellord1, axiom,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v1_relat_1 @ A ) =>
% 0.16/0.48       ( ( v2_wellord1 @ A ) =>
% 0.16/0.48         ( ![B:$i]:
% 0.16/0.48           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.16/0.48                ( r4_wellord1 @
% 0.16/0.48                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.16/0.48  thf('22', plain,
% 0.16/0.48      (![X10 : $i, X11 : $i]:
% 0.16/0.48         (~ (v2_wellord1 @ X10)
% 0.16/0.48          | ~ (r4_wellord1 @ X10 @ 
% 0.16/0.48               (k2_wellord1 @ X10 @ (k1_wellord1 @ X10 @ X11)))
% 0.16/0.48          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.16/0.48          | ~ (v1_relat_1 @ X10))),
% 0.16/0.48      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.16/0.48  thf('23', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.16/0.48             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.16/0.48          | (r1_tarski @ X1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.16/0.48          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.16/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.16/0.48  thf('24', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.16/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.16/0.48  thf(d1_wellord2, axiom,
% 0.16/0.48    (![A:$i,B:$i]:
% 0.16/0.48     ( ( v1_relat_1 @ B ) =>
% 0.16/0.48       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.16/0.48         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.16/0.48           ( ![C:$i,D:$i]:
% 0.16/0.48             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.16/0.48               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.16/0.48                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.16/0.48  thf('25', plain,
% 0.16/0.48      (![X12 : $i, X13 : $i]:
% 0.16/0.48         (((X13) != (k1_wellord2 @ X12))
% 0.16/0.48          | ((k3_relat_1 @ X13) = (X12))
% 0.16/0.48          | ~ (v1_relat_1 @ X13))),
% 0.16/0.48      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.16/0.48  thf('26', plain,
% 0.16/0.48      (![X12 : $i]:
% 0.16/0.48         (~ (v1_relat_1 @ (k1_wellord2 @ X12))
% 0.16/0.48          | ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12)))),
% 0.16/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.16/0.48  thf('27', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.16/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.16/0.48  thf('28', plain, (![X12 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12))),
% 0.16/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.16/0.48  thf('29', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.16/0.48             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.16/0.48          | (r1_tarski @ X1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.16/0.48      inference('demod', [status(thm)], ['23', '24', '28'])).
% 0.16/0.48  thf('30', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0)
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.16/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['17', '29'])).
% 0.16/0.48  thf('31', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.16/0.48          | (r1_tarski @ X1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.16/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.16/0.48  thf('32', plain,
% 0.16/0.48      ((~ (v1_ordinal1 @ sk_B_1)
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_B_1)
% 0.16/0.48        | ((sk_A) = (sk_B_1))
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | ~ (v1_ordinal1 @ sk_A)
% 0.16/0.48        | (r1_tarski @ sk_B_1 @ sk_A)
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))
% 0.16/0.48        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['12', '31'])).
% 0.16/0.48  thf('33', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf(cc1_ordinal1, axiom,
% 0.16/0.48    (![A:$i]:
% 0.16/0.48     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.16/0.48  thf('34', plain, (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.16/0.48      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.16/0.48  thf('35', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.16/0.48  thf('36', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('39', plain, (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.16/0.48      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.16/0.48  thf('40', plain, ((v1_ordinal1 @ sk_A)),
% 0.16/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.16/0.48  thf('41', plain,
% 0.16/0.48      ((((sk_A) = (sk_B_1))
% 0.16/0.48        | (r1_tarski @ sk_B_1 @ sk_A)
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))
% 0.16/0.48        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('demod', [status(thm)], ['32', '35', '36', '37', '40'])).
% 0.16/0.48  thf('42', plain, (((sk_A) != (sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('43', plain,
% 0.16/0.48      (((r1_tarski @ sk_B_1 @ sk_A)
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))
% 0.16/0.48        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.16/0.48  thf('44', plain,
% 0.16/0.48      ((~ (v3_ordinal1 @ sk_B_1)
% 0.16/0.48        | ~ (r2_hidden @ sk_A @ sk_B_1)
% 0.16/0.48        | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('sup-', [status(thm)], ['6', '43'])).
% 0.16/0.48  thf('45', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('46', plain,
% 0.16/0.48      ((~ (r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.16/0.48  thf('47', plain,
% 0.16/0.48      (((r1_tarski @ sk_B_1 @ sk_A)
% 0.16/0.48        | ~ (v1_ordinal1 @ sk_A)
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_B_1)
% 0.16/0.48        | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('sup-', [status(thm)], ['5', '46'])).
% 0.16/0.48  thf('48', plain, ((v1_ordinal1 @ sk_A)),
% 0.16/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.16/0.48  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('50', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('51', plain,
% 0.16/0.48      (((r1_tarski @ sk_B_1 @ sk_A)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.16/0.48  thf('52', plain, ((((sk_B_1) = (sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('simplify', [status(thm)], ['51'])).
% 0.16/0.48  thf('53', plain, (((sk_A) != (sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('54', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.16/0.48  thf('55', plain,
% 0.16/0.48      (![X20 : $i, X21 : $i]:
% 0.16/0.48         (((k2_wellord1 @ (k1_wellord2 @ X21) @ X20) = (k1_wellord2 @ X20))
% 0.16/0.48          | ~ (r1_tarski @ X20 @ X21))),
% 0.16/0.48      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.16/0.48  thf('56', plain,
% 0.16/0.48      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B_1) = (k1_wellord2 @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['54', '55'])).
% 0.16/0.48  thf('57', plain,
% 0.16/0.48      (![X6 : $i, X7 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X6)
% 0.16/0.48          | (r2_hidden @ X7 @ X6)
% 0.16/0.48          | ((X7) = (X6))
% 0.16/0.48          | (r2_hidden @ X6 @ X7)
% 0.16/0.48          | ~ (v3_ordinal1 @ X7))),
% 0.16/0.48      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.16/0.48  thf('58', plain,
% 0.16/0.48      (![X17 : $i, X18 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X17)
% 0.16/0.48          | ((X18) = (k1_wellord1 @ (k1_wellord2 @ X17) @ X18))
% 0.16/0.48          | ~ (r2_hidden @ X18 @ X17)
% 0.16/0.48          | ~ (v3_ordinal1 @ X18))),
% 0.16/0.48      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.16/0.48  thf('59', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X1)
% 0.16/0.48          | (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.16/0.48  thf('60', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ~ (v3_ordinal1 @ X1))),
% 0.16/0.48      inference('simplify', [status(thm)], ['59'])).
% 0.16/0.48  thf('61', plain,
% 0.16/0.48      (![X10 : $i, X11 : $i]:
% 0.16/0.48         (~ (v2_wellord1 @ X10)
% 0.16/0.48          | ~ (r4_wellord1 @ X10 @ 
% 0.16/0.48               (k2_wellord1 @ X10 @ (k1_wellord1 @ X10 @ X11)))
% 0.16/0.48          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.16/0.48          | ~ (v1_relat_1 @ X10))),
% 0.16/0.48      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.16/0.48  thf('62', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.16/0.48             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | (r2_hidden @ X1 @ X0)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.16/0.48          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.16/0.48      inference('sup-', [status(thm)], ['60', '61'])).
% 0.16/0.48  thf('63', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.16/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.16/0.48  thf('64', plain, (![X12 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12))),
% 0.16/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.16/0.48  thf('65', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.16/0.48             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | (r2_hidden @ X1 @ X0)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.16/0.48      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.16/0.48  thf('66', plain,
% 0.16/0.48      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1)
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['56', '65'])).
% 0.16/0.48  thf('67', plain,
% 0.16/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('68', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('69', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('70', plain,
% 0.16/0.48      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.16/0.48  thf('71', plain, (((sk_A) != (sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('72', plain,
% 0.16/0.48      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.16/0.48  thf('73', plain,
% 0.16/0.48      ((~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1)
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('sup-', [status(thm)], ['2', '72'])).
% 0.16/0.48  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('75', plain,
% 0.16/0.48      (((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['73', '74'])).
% 0.16/0.48  thf('76', plain,
% 0.16/0.48      ((~ (v3_ordinal1 @ sk_B_1)
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['1', '75'])).
% 0.16/0.48  thf('77', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('78', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('79', plain,
% 0.16/0.48      (((r2_hidden @ sk_A @ sk_B_1)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.16/0.48  thf('80', plain, ((((sk_B_1) = (sk_A)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('simplify', [status(thm)], ['79'])).
% 0.16/0.48  thf('81', plain, (((sk_A) != (sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('82', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.16/0.48  thf('83', plain,
% 0.16/0.48      (![X17 : $i, X18 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X17)
% 0.16/0.48          | ((X18) = (k1_wellord1 @ (k1_wellord2 @ X17) @ X18))
% 0.16/0.48          | ~ (r2_hidden @ X18 @ X17)
% 0.16/0.48          | ~ (v3_ordinal1 @ X18))),
% 0.16/0.48      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.16/0.48  thf('84', plain,
% 0.16/0.48      ((~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['82', '83'])).
% 0.16/0.48  thf('85', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('86', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('87', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.16/0.48  thf('88', plain,
% 0.16/0.48      (![X10 : $i, X11 : $i]:
% 0.16/0.48         (~ (v2_wellord1 @ X10)
% 0.16/0.48          | ~ (r4_wellord1 @ X10 @ 
% 0.16/0.48               (k2_wellord1 @ X10 @ (k1_wellord1 @ X10 @ X11)))
% 0.16/0.48          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.16/0.48          | ~ (v1_relat_1 @ X10))),
% 0.16/0.48      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.16/0.48  thf('89', plain,
% 0.16/0.48      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ 
% 0.16/0.48           (k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A))
% 0.16/0.48        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B_1))
% 0.16/0.48        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B_1)))
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1)))),
% 0.16/0.48      inference('sup-', [status(thm)], ['87', '88'])).
% 0.16/0.48  thf('90', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (v3_ordinal1 @ X1)
% 0.16/0.48          | (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ((X1) = (X0))
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | (r1_tarski @ X1 @ X0))),
% 0.16/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.16/0.48  thf('91', plain,
% 0.16/0.48      (![X19 : $i]:
% 0.16/0.48         ((v2_wellord1 @ (k1_wellord2 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.16/0.48      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.16/0.48  thf('92', plain,
% 0.16/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('93', plain,
% 0.16/0.48      (![X0 : $i, X1 : $i]:
% 0.16/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.16/0.48          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.16/0.48          | (r1_tarski @ X1 @ X0)
% 0.16/0.48          | ~ (v1_ordinal1 @ X0)
% 0.16/0.48          | ~ (v3_ordinal1 @ X0)
% 0.16/0.48          | ((X0) = (X1))
% 0.16/0.48          | ~ (v3_ordinal1 @ X1)
% 0.16/0.48          | ~ (v1_ordinal1 @ X1)
% 0.16/0.48          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.16/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.16/0.48  thf('94', plain,
% 0.16/0.48      ((~ (v1_ordinal1 @ sk_A)
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | ((sk_B_1) = (sk_A))
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_B_1)
% 0.16/0.48        | ~ (v1_ordinal1 @ sk_B_1)
% 0.16/0.48        | (r1_tarski @ sk_A @ sk_B_1)
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('sup-', [status(thm)], ['92', '93'])).
% 0.16/0.48  thf('95', plain, ((v1_ordinal1 @ sk_A)),
% 0.16/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.16/0.48  thf('96', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('97', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('98', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.16/0.48  thf('99', plain,
% 0.16/0.48      ((((sk_B_1) = (sk_A))
% 0.16/0.48        | (r1_tarski @ sk_A @ sk_B_1)
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.16/0.48  thf('100', plain, (((sk_A) != (sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('101', plain,
% 0.16/0.48      (((r1_tarski @ sk_A @ sk_B_1)
% 0.16/0.48        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A))),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 0.16/0.48  thf('102', plain,
% 0.16/0.48      ((~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | ~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.16/0.48        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['91', '101'])).
% 0.16/0.48  thf('103', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('104', plain,
% 0.16/0.48      ((~ (r2_hidden @ sk_B_1 @ sk_A) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('demod', [status(thm)], ['102', '103'])).
% 0.16/0.48  thf('105', plain,
% 0.16/0.48      (((r1_tarski @ sk_A @ sk_B_1)
% 0.16/0.48        | ~ (v1_ordinal1 @ sk_B_1)
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_B_1)
% 0.16/0.48        | ((sk_A) = (sk_B_1))
% 0.16/0.48        | ~ (v3_ordinal1 @ sk_A)
% 0.16/0.48        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('sup-', [status(thm)], ['90', '104'])).
% 0.16/0.48  thf('106', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.16/0.48  thf('107', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('108', plain, ((v3_ordinal1 @ sk_A)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('109', plain,
% 0.16/0.48      (((r1_tarski @ sk_A @ sk_B_1)
% 0.16/0.48        | ((sk_A) = (sk_B_1))
% 0.16/0.48        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.16/0.48  thf('110', plain, ((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.16/0.48      inference('simplify', [status(thm)], ['109'])).
% 0.16/0.48  thf('111', plain, (((sk_A) != (sk_B_1))),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('112', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 0.16/0.48  thf('113', plain,
% 0.16/0.48      (![X20 : $i, X21 : $i]:
% 0.16/0.48         (((k2_wellord1 @ (k1_wellord2 @ X21) @ X20) = (k1_wellord2 @ X20))
% 0.16/0.48          | ~ (r1_tarski @ X20 @ X21))),
% 0.16/0.48      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.16/0.48  thf('114', plain,
% 0.16/0.48      (((k2_wellord1 @ (k1_wellord2 @ sk_B_1) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.16/0.48      inference('sup-', [status(thm)], ['112', '113'])).
% 0.16/0.48  thf('115', plain,
% 0.16/0.48      ((r4_wellord1 @ (k1_wellord2 @ sk_B_1) @ (k1_wellord2 @ sk_A))),
% 0.16/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.16/0.48  thf('116', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.16/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.16/0.48  thf('117', plain,
% 0.16/0.48      (![X12 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12))),
% 0.16/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.16/0.48  thf('118', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.16/0.48      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.16/0.48  thf('119', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B_1))),
% 0.16/0.48      inference('demod', [status(thm)],
% 0.16/0.48                ['89', '114', '115', '116', '117', '118'])).
% 0.16/0.48  thf('120', plain, (~ (v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('sup-', [status(thm)], ['0', '119'])).
% 0.16/0.48  thf('121', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.16/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.48  thf('122', plain, ($false), inference('demod', [status(thm)], ['120', '121'])).
% 0.16/0.48  
% 0.16/0.48  % SZS output end Refutation
% 0.16/0.48  
% 0.16/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
