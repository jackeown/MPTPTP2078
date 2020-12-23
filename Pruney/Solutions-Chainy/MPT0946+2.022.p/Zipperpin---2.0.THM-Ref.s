%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jjJe2nRIDE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 266 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   29
%              Number of atoms          :  751 (2417 expanded)
%              Number of equality atoms :   35 ( 135 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X22: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
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

thf('3',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( X21
        = ( k1_wellord1 @ ( k1_wellord2 @ X20 ) @ X21 ) )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X22: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X9 @ ( k1_wellord1 @ X9 @ X10 ) ) )
        = ( k1_wellord1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

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

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16
       != ( k1_wellord2 @ X15 ) )
      | ( ( k3_relat_1 @ X16 )
        = X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('11',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X15 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X15 ) )
        = X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('13',plain,(
    ! [X15: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) )
      | ( r2_hidden @ X6 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X24 ) @ X23 )
        = ( k1_wellord2 @ X23 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
        = ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_wellord1 @ X13 )
      | ~ ( r4_wellord1 @ X13 @ ( k2_wellord1 @ X13 @ ( k1_wellord1 @ X13 @ X14 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( X21
        = ( k1_wellord1 @ ( k1_wellord2 @ X20 ) @ X21 ) )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('53',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('58',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r4_wellord1 @ X11 @ X12 )
      | ~ ( r4_wellord1 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('63',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('64',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('66',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','64','65','66'])).

thf('68',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jjJe2nRIDE
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 145 iterations in 0.114s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.37/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.57  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.37/0.57  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.37/0.57  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(t7_wellord2, axiom,
% 0.37/0.57    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X22 : $i]:
% 0.37/0.57         ((v2_wellord1 @ (k1_wellord2 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.37/0.57  thf(t24_ordinal1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.57           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.37/0.57                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X4)
% 0.37/0.57          | (r2_hidden @ X5 @ X4)
% 0.37/0.57          | ((X5) = (X4))
% 0.37/0.57          | (r2_hidden @ X4 @ X5)
% 0.37/0.57          | ~ (v3_ordinal1 @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X22 : $i]:
% 0.37/0.57         ((v2_wellord1 @ (k1_wellord2 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.37/0.57  thf(t11_wellord2, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.57           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.37/0.57             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.57              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.37/0.57                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X4)
% 0.37/0.57          | (r2_hidden @ X5 @ X4)
% 0.37/0.57          | ((X5) = (X4))
% 0.37/0.57          | (r2_hidden @ X4 @ X5)
% 0.37/0.57          | ~ (v3_ordinal1 @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.37/0.57  thf(t10_wellord2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.57           ( ( r2_hidden @ A @ B ) =>
% 0.37/0.57             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X20)
% 0.37/0.57          | ((X21) = (k1_wellord1 @ (k1_wellord2 @ X20) @ X21))
% 0.37/0.57          | ~ (r2_hidden @ X21 @ X20)
% 0.37/0.57          | ~ (v3_ordinal1 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X1)
% 0.37/0.57          | ((X1) = (X0))
% 0.37/0.57          | ~ (v3_ordinal1 @ X0)
% 0.37/0.57          | ~ (v3_ordinal1 @ X1)
% 0.37/0.57          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.37/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.37/0.57          | ~ (v3_ordinal1 @ X0)
% 0.37/0.57          | ((X1) = (X0))
% 0.37/0.57          | (r2_hidden @ X0 @ X1)
% 0.37/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X22 : $i]:
% 0.37/0.57         ((v2_wellord1 @ (k1_wellord2 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.37/0.57  thf(t40_wellord1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ B ) =>
% 0.37/0.57       ( ( v2_wellord1 @ B ) =>
% 0.37/0.57         ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) ) =
% 0.37/0.57           ( k1_wellord1 @ B @ A ) ) ) ))).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (v2_wellord1 @ X9)
% 0.37/0.57          | ((k3_relat_1 @ (k2_wellord1 @ X9 @ (k1_wellord1 @ X9 @ X10)))
% 0.37/0.57              = (k1_wellord1 @ X9 @ X10))
% 0.37/0.57          | ~ (v1_relat_1 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.37/0.57  thf(d1_wellord2, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ B ) =>
% 0.37/0.57       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.37/0.57         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.37/0.57           ( ![C:$i,D:$i]:
% 0.37/0.57             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.37/0.57               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.37/0.57                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X15 : $i, X16 : $i]:
% 0.37/0.57         (((X16) != (k1_wellord2 @ X15))
% 0.37/0.57          | ((k3_relat_1 @ X16) = (X15))
% 0.37/0.57          | ~ (v1_relat_1 @ X16))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X15 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ (k1_wellord2 @ X15))
% 0.37/0.57          | ((k3_relat_1 @ (k1_wellord2 @ X15)) = (X15)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.57  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.37/0.57  thf('12', plain, (![X19 : $i]: (v1_relat_1 @ (k1_wellord2 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.57  thf('13', plain, (![X15 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X15)) = (X15))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf(d3_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf(t19_wellord1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ C ) =>
% 0.37/0.57       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 0.37/0.57         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X6 @ (k3_relat_1 @ (k2_wellord1 @ X7 @ X8)))
% 0.37/0.57          | (r2_hidden @ X6 @ (k3_relat_1 @ X7))
% 0.37/0.57          | ~ (v1_relat_1 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.37/0.57          | ~ (v1_relat_1 @ X1)
% 0.37/0.57          | (r2_hidden @ 
% 0.37/0.57             (sk_C @ X2 @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0))) @ 
% 0.37/0.57             (k3_relat_1 @ X1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ X0)
% 0.37/0.57          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.37/0.57             (k3_relat_1 @ X0))
% 0.37/0.57          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.37/0.57             (k3_relat_1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.37/0.57           (k3_relat_1 @ X0))
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ 
% 0.37/0.57           (k3_relat_1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1)) @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '19'])).
% 0.37/0.57  thf('21', plain, (![X19 : $i]: (v1_relat_1 @ (k1_wellord2 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1)) @ 
% 0.37/0.57          X0)),
% 0.37/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0) @ X1)
% 0.37/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['9', '22'])).
% 0.37/0.57  thf('24', plain, (![X19 : $i]: (v1_relat_1 @ (k1_wellord2 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0) @ X1)
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X0)
% 0.37/0.57          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['8', '25'])).
% 0.37/0.57  thf(t8_wellord2, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.37/0.57       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i]:
% 0.37/0.57         (((k2_wellord1 @ (k1_wellord2 @ X24) @ X23) = (k1_wellord2 @ X23))
% 0.37/0.57          | ~ (r1_tarski @ X23 @ X24))),
% 0.37/0.57      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X0)
% 0.37/0.57          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ 
% 0.37/0.57              (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.37/0.57              = (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf(t57_wellord1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ( v2_wellord1 @ A ) =>
% 0.37/0.57         ( ![B:$i]:
% 0.37/0.57           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.37/0.57                ( r4_wellord1 @
% 0.37/0.57                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         (~ (v2_wellord1 @ X13)
% 0.37/0.57          | ~ (r4_wellord1 @ X13 @ 
% 0.37/0.57               (k2_wellord1 @ X13 @ (k1_wellord1 @ X13 @ X14)))
% 0.37/0.57          | ~ (r2_hidden @ X14 @ (k3_relat_1 @ X13))
% 0.37/0.57          | ~ (v1_relat_1 @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.37/0.57             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.37/0.57          | ~ (v3_ordinal1 @ X1)
% 0.37/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.57  thf('31', plain, (![X19 : $i]: (v1_relat_1 @ (k1_wellord2 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.57  thf('32', plain, (![X15 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X15)) = (X15))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.37/0.57             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.37/0.57          | ~ (v3_ordinal1 @ X1)
% 0.37/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.37/0.57          | ~ (v3_ordinal1 @ X0)
% 0.37/0.57          | (r2_hidden @ X1 @ X0)
% 0.37/0.57          | ((X0) = (X1))
% 0.37/0.57          | ~ (v3_ordinal1 @ X1)
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '33'])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.37/0.57          | ~ (v3_ordinal1 @ X1)
% 0.37/0.57          | ((X0) = (X1))
% 0.37/0.57          | (r2_hidden @ X1 @ X0)
% 0.37/0.57          | ~ (v3_ordinal1 @ X0)
% 0.37/0.57          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.37/0.57        | (r2_hidden @ sk_A @ sk_B)
% 0.37/0.57        | ((sk_B) = (sk_A))
% 0.37/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.37/0.57        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '35'])).
% 0.37/0.57  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.37/0.57        | ((sk_B) = (sk_A))
% 0.37/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.37/0.57        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.57  thf('40', plain, (((sk_A) != (sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.37/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.37/0.57        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.37/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.37/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '41'])).
% 0.37/0.57  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('44', plain, ((~ (r2_hidden @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.37/0.57        | (r2_hidden @ sk_A @ sk_B)
% 0.37/0.57        | ((sk_B) = (sk_A))
% 0.37/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '44'])).
% 0.37/0.57  thf('46', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.37/0.57        | ((sk_B) = (sk_A))
% 0.37/0.57        | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.37/0.57  thf('49', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.57  thf('50', plain, (((sk_A) != (sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('51', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (v3_ordinal1 @ X20)
% 0.37/0.57          | ((X21) = (k1_wellord1 @ (k1_wellord2 @ X20) @ X21))
% 0.37/0.57          | ~ (r2_hidden @ X21 @ X20)
% 0.37/0.57          | ~ (v3_ordinal1 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.37/0.57        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.37/0.57        | ~ (v3_ordinal1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('56', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.37/0.57             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.37/0.57          | ~ (v3_ordinal1 @ X1)
% 0.37/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.37/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.37/0.57        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.37/0.57        | ~ (v3_ordinal1 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t50_wellord1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( v1_relat_1 @ B ) =>
% 0.37/0.57           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ X11)
% 0.37/0.57          | (r4_wellord1 @ X11 @ X12)
% 0.37/0.57          | ~ (r4_wellord1 @ X12 @ X11)
% 0.37/0.57          | ~ (v1_relat_1 @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.37/0.57        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.37/0.57        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.57  thf('62', plain, (![X19 : $i]: (v1_relat_1 @ (k1_wellord2 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.57  thf('63', plain, (![X19 : $i]: (v1_relat_1 @ (k1_wellord2 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.37/0.57  thf('65', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf('66', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('67', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['58', '64', '65', '66'])).
% 0.37/0.57  thf('68', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '67'])).
% 0.37/0.57  thf('69', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('70', plain, ($false), inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
