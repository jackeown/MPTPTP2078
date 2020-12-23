%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tJq5vofZe7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 249 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   28
%              Number of atoms          :  721 (2316 expanded)
%              Number of equality atoms :   35 ( 134 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
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

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k3_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      = ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('50',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('55',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('60',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('61',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('63',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','61','62'])).

thf('64',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tJq5vofZe7
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 82 iterations in 0.110s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.21/0.56  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.56  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(t7_wellord2, axiom,
% 0.21/0.56    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X26 : $i]:
% 0.21/0.56         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.21/0.56  thf(t24_ordinal1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.56                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X7)
% 0.21/0.56          | (r2_hidden @ X8 @ X7)
% 0.21/0.56          | ((X8) = (X7))
% 0.21/0.56          | (r2_hidden @ X7 @ X8)
% 0.21/0.56          | ~ (v3_ordinal1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X26 : $i]:
% 0.21/0.56         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.21/0.56  thf(t11_wellord2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.21/0.56             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.21/0.56                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X7)
% 0.21/0.56          | (r2_hidden @ X8 @ X7)
% 0.21/0.56          | ((X8) = (X7))
% 0.21/0.56          | (r2_hidden @ X7 @ X8)
% 0.21/0.56          | ~ (v3_ordinal1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.21/0.56  thf(t10_wellord2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56           ( ( r2_hidden @ A @ B ) =>
% 0.21/0.56             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X24)
% 0.21/0.56          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.21/0.56          | ~ (r2_hidden @ X25 @ X24)
% 0.21/0.56          | ~ (v3_ordinal1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X1)
% 0.21/0.56          | (r2_hidden @ X0 @ X1)
% 0.21/0.56          | ((X1) = (X0))
% 0.21/0.56          | ~ (v3_ordinal1 @ X0)
% 0.21/0.56          | ~ (v3_ordinal1 @ X1)
% 0.21/0.56          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.56          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.56          | ~ (v3_ordinal1 @ X0)
% 0.21/0.56          | ((X1) = (X0))
% 0.21/0.56          | (r2_hidden @ X0 @ X1)
% 0.21/0.56          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf(d1_wellord2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.56         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.56           ( ![C:$i,D:$i]:
% 0.21/0.56             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.56               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.56                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         (((X20) != (k1_wellord2 @ X19))
% 0.21/0.56          | ((k3_relat_1 @ X20) = (X19))
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X19 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.21/0.56          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.56  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.56  thf('10', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.56  thf('11', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf(d3_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf(d1_wellord1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i,C:$i]:
% 0.21/0.56         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.21/0.56           ( ![D:$i]:
% 0.21/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.56               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         (((X12) != (k1_wellord1 @ X11 @ X10))
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11)
% 0.21/0.56          | ~ (r2_hidden @ X13 @ X12)
% 0.21/0.56          | ~ (v1_relat_1 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X11)
% 0.21/0.56          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X11 @ X10))
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11))),
% 0.21/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.21/0.56          | ~ (v1_relat_1 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.56  thf(t30_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ C ) =>
% 0.21/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.56         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.56           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.21/0.56          | (r2_hidden @ X4 @ (k3_relat_1 @ X6))
% 0.21/0.56          | ~ (v1_relat_1 @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.21/0.56             (k3_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.21/0.56           (k3_relat_1 @ X0))
% 0.21/0.56          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.21/0.56          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['11', '21'])).
% 0.21/0.56  thf('23', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)),
% 0.21/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf(t8_wellord2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.56       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i]:
% 0.21/0.56         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.21/0.56          | ~ (r1_tarski @ X27 @ X28))),
% 0.21/0.56      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k2_wellord1 @ (k1_wellord2 @ X0) @ 
% 0.21/0.56           (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.56           = (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(t57_wellord1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ( v2_wellord1 @ A ) =>
% 0.21/0.56         ( ![B:$i]:
% 0.21/0.56           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.21/0.56                ( r4_wellord1 @
% 0.21/0.56                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (~ (v2_wellord1 @ X17)
% 0.21/0.56          | ~ (r4_wellord1 @ X17 @ 
% 0.21/0.56               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.21/0.56          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.21/0.56          | ~ (v1_relat_1 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.56             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.56          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.21/0.56          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.56  thf('30', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.56             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.21/0.56          | ~ (v3_ordinal1 @ X0)
% 0.21/0.56          | (r2_hidden @ X1 @ X0)
% 0.21/0.56          | ((X0) = (X1))
% 0.21/0.56          | ~ (v3_ordinal1 @ X1)
% 0.21/0.56          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.56        | ~ (v3_ordinal1 @ sk_A)
% 0.21/0.56        | ((sk_B) = (sk_A))
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.56        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '32'])).
% 0.21/0.56  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.56        | ((sk_B) = (sk_A))
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.56  thf('37', plain, (((sk_A) != (sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '38'])).
% 0.21/0.56  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain, (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ sk_B)
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.56        | ((sk_B) = (sk_A))
% 0.21/0.56        | ~ (v3_ordinal1 @ sk_A)
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '41'])).
% 0.21/0.56  thf('43', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ sk_B)
% 0.21/0.56        | ((sk_B) = (sk_A))
% 0.21/0.56        | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.56  thf('46', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.56  thf('47', plain, (((sk_A) != (sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('48', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X24)
% 0.21/0.56          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.21/0.56          | ~ (r2_hidden @ X25 @ X24)
% 0.21/0.56          | ~ (v3_ordinal1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.56        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.21/0.56        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.56  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('52', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.56             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.21/0.56        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.21/0.56        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t50_wellord1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v1_relat_1 @ B ) =>
% 0.21/0.56           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X15)
% 0.21/0.56          | (r4_wellord1 @ X15 @ X16)
% 0.21/0.56          | ~ (r4_wellord1 @ X16 @ X15)
% 0.21/0.56          | ~ (v1_relat_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.21/0.56        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.21/0.56        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('59', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.56  thf('60', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.56  thf('62', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('63', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['55', '61', '62'])).
% 0.21/0.56  thf('64', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '63'])).
% 0.21/0.56  thf('65', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('66', plain, ($false), inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
