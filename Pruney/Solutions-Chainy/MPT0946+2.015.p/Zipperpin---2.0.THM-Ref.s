%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9MdWrbvvi

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:30 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 915 expanded)
%              Number of leaves         :   26 ( 272 expanded)
%              Depth                    :   46
%              Number of atoms          : 1572 (10067 expanded)
%              Number of equality atoms :   95 ( 634 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
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
    ! [X27: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_ordinal1 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_ordinal1 @ X6 ) )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('8',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( X26
        = ( k1_wellord1 @ ( k1_wellord2 @ X25 ) @ X26 ) )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0
        = ( k1_wellord1 @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X9 ) )
      | ~ ( v3_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_wellord1 @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k1_wellord1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_wellord1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_wellord2 @ X20 ) )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ( r1_tarski @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('21',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ ( k1_wellord2 @ X20 ) )
      | ( r1_tarski @ X22 @ X23 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ~ ( r2_hidden @ X22 @ X20 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ ( k1_wellord2 @ X20 ) )
      | ( r1_tarski @ X22 @ X23 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ~ ( r2_hidden @ X22 @ X20 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X27: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
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

thf('30',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r4_wellord1 @ X16 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('34',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('35',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_ordinal1 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ ( k1_ordinal1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ ( k1_wellord2 @ X20 ) )
      | ( r1_tarski @ X22 @ X23 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ~ ( r2_hidden @ X22 @ X20 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('49',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X29 ) @ X28 )
        = ( k1_wellord2 @ X28 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( X26
        = ( k1_wellord1 @ ( k1_wellord2 @ X25 ) @ X26 ) )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ~ ( r4_wellord1 @ X18 @ ( k2_wellord1 @ X18 @ ( k1_wellord1 @ X18 @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21
       != ( k1_wellord2 @ X20 ) )
      | ( ( k3_relat_1 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('59',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X20 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X20 ) )
        = X20 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('61',plain,(
    ! [X20: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','64'])).

thf('66',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_B = sk_A )
    | ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','70'])).

thf('72',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','73'])).

thf('75',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_B = sk_A )
    | ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X29 ) @ X28 )
        = ( k1_wellord2 @ X28 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('82',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('84',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( X26
        = ( k1_wellord1 @ ( k1_wellord2 @ X25 ) @ X26 ) )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ~ ( r4_wellord1 @ X18 @ ( k2_wellord1 @ X18 @ ( k1_wellord1 @ X18 @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('90',plain,(
    ! [X20: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','98'])).

thf('100',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','101'])).

thf('103',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( X26
        = ( k1_wellord1 @ ( k1_wellord2 @ X25 ) @ X26 ) )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('110',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_wellord1 @ X18 )
      | ~ ( r4_wellord1 @ X18 @ ( k2_wellord1 @ X18 @ ( k1_wellord1 @ X18 @ X19 ) ) )
      | ~ ( r2_hidden @ X19 @ ( k3_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('115',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('117',plain,(
    ! [X27: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('118',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('120',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( sk_A = sk_B )
    | ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['116','128'])).

thf('130',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_A = sk_B )
    | ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X29 ) @ X28 )
        = ( k1_wellord2 @ X28 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('137',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('139',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('140',plain,(
    ! [X20: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('141',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('142',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','137','138','139','140','141'])).

thf('143',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','142'])).

thf('144',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9MdWrbvvi
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.49/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.65  % Solved by: fo/fo7.sh
% 0.49/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.65  % done 209 iterations in 0.192s
% 0.49/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.65  % SZS output start Refutation
% 0.49/0.65  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.49/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.65  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.49/0.65  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.49/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.65  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.49/0.65  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.49/0.65  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.49/0.65  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.49/0.65  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.49/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.65  thf(t7_wellord2, axiom,
% 0.49/0.65    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.49/0.65  thf('0', plain,
% 0.49/0.65      (![X27 : $i]:
% 0.49/0.65         ((v2_wellord1 @ (k1_wellord2 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 0.49/0.65      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.49/0.65  thf(t24_ordinal1, axiom,
% 0.49/0.65    (![A:$i]:
% 0.49/0.65     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.65       ( ![B:$i]:
% 0.49/0.65         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.65           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.49/0.65                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.49/0.65  thf('1', plain,
% 0.49/0.65      (![X7 : $i, X8 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X7)
% 0.49/0.65          | (r2_hidden @ X8 @ X7)
% 0.49/0.65          | ((X8) = (X7))
% 0.49/0.65          | (r2_hidden @ X7 @ X8)
% 0.49/0.65          | ~ (v3_ordinal1 @ X8))),
% 0.49/0.65      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.49/0.65  thf('2', plain,
% 0.49/0.65      (![X27 : $i]:
% 0.49/0.65         ((v2_wellord1 @ (k1_wellord2 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 0.49/0.65      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.49/0.65  thf('3', plain,
% 0.49/0.65      (![X7 : $i, X8 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X7)
% 0.49/0.65          | (r2_hidden @ X8 @ X7)
% 0.49/0.65          | ((X8) = (X7))
% 0.49/0.65          | (r2_hidden @ X7 @ X8)
% 0.49/0.65          | ~ (v3_ordinal1 @ X8))),
% 0.49/0.65      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.49/0.65  thf(t13_ordinal1, axiom,
% 0.49/0.65    (![A:$i,B:$i]:
% 0.49/0.65     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.49/0.65       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.49/0.65  thf('4', plain,
% 0.49/0.65      (![X5 : $i, X6 : $i]:
% 0.49/0.65         ((r2_hidden @ X5 @ (k1_ordinal1 @ X6)) | ~ (r2_hidden @ X5 @ X6))),
% 0.49/0.65      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.49/0.65  thf('5', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.49/0.65  thf('6', plain,
% 0.49/0.65      (![X7 : $i, X8 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X7)
% 0.49/0.65          | (r2_hidden @ X8 @ X7)
% 0.49/0.65          | ((X8) = (X7))
% 0.49/0.65          | (r2_hidden @ X7 @ X8)
% 0.49/0.65          | ~ (v3_ordinal1 @ X8))),
% 0.49/0.65      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.49/0.65  thf('7', plain,
% 0.49/0.65      (![X5 : $i, X6 : $i]:
% 0.49/0.65         ((r2_hidden @ X5 @ (k1_ordinal1 @ X6)) | ((X5) != (X6)))),
% 0.49/0.65      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.49/0.65  thf('8', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.49/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.49/0.65  thf(t10_wellord2, axiom,
% 0.49/0.65    (![A:$i]:
% 0.49/0.65     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.65       ( ![B:$i]:
% 0.49/0.65         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.65           ( ( r2_hidden @ A @ B ) =>
% 0.49/0.65             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.49/0.65  thf('9', plain,
% 0.49/0.65      (![X25 : $i, X26 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X25)
% 0.49/0.65          | ((X26) = (k1_wellord1 @ (k1_wellord2 @ X25) @ X26))
% 0.49/0.65          | ~ (r2_hidden @ X26 @ X25)
% 0.49/0.65          | ~ (v3_ordinal1 @ X26))),
% 0.49/0.65      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.49/0.65  thf('10', plain,
% 0.49/0.65      (![X0 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X0) = (k1_wellord1 @ (k1_wellord2 @ (k1_ordinal1 @ X0)) @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.65  thf(t29_ordinal1, axiom,
% 0.49/0.65    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.49/0.65  thf('11', plain,
% 0.49/0.65      (![X9 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X9)) | ~ (v3_ordinal1 @ X9))),
% 0.49/0.65      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.49/0.65  thf('12', plain,
% 0.49/0.65      (![X0 : $i]:
% 0.49/0.65         (((X0) = (k1_wellord1 @ (k1_wellord2 @ (k1_ordinal1 @ X0)) @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('clc', [status(thm)], ['10', '11'])).
% 0.49/0.65  thf(d1_wellord1, axiom,
% 0.49/0.65    (![A:$i]:
% 0.49/0.65     ( ( v1_relat_1 @ A ) =>
% 0.49/0.65       ( ![B:$i,C:$i]:
% 0.49/0.65         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.49/0.65           ( ![D:$i]:
% 0.49/0.65             ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.65               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.49/0.65  thf('13', plain,
% 0.49/0.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.65         (((X13) != (k1_wellord1 @ X12 @ X11))
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X14 @ X11) @ X12)
% 0.49/0.65          | ~ (r2_hidden @ X14 @ X13)
% 0.49/0.65          | ~ (v1_relat_1 @ X12))),
% 0.49/0.65      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.49/0.65  thf('14', plain,
% 0.49/0.65      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.49/0.65         (~ (v1_relat_1 @ X12)
% 0.49/0.65          | ~ (r2_hidden @ X14 @ (k1_wellord1 @ X12 @ X11))
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X14 @ X11) @ X12))),
% 0.49/0.65      inference('simplify', [status(thm)], ['13'])).
% 0.49/0.65  thf('15', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65             (k1_wellord2 @ (k1_ordinal1 @ X0)))
% 0.49/0.65          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_ordinal1 @ X0))))),
% 0.49/0.65      inference('sup-', [status(thm)], ['12', '14'])).
% 0.49/0.65  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.49/0.65  thf('16', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('17', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65             (k1_wellord2 @ (k1_ordinal1 @ X0))))),
% 0.49/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.49/0.65  thf('18', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65             (k1_wellord2 @ (k1_ordinal1 @ X0)))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['6', '17'])).
% 0.49/0.65  thf('19', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65           (k1_wellord2 @ (k1_ordinal1 @ X0)))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.65      inference('simplify', [status(thm)], ['18'])).
% 0.49/0.65  thf(d1_wellord2, axiom,
% 0.49/0.65    (![A:$i,B:$i]:
% 0.49/0.65     ( ( v1_relat_1 @ B ) =>
% 0.49/0.65       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.49/0.65         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.49/0.65           ( ![C:$i,D:$i]:
% 0.49/0.65             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.49/0.65               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.49/0.65                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.49/0.65  thf('20', plain,
% 0.49/0.65      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.65         (((X21) != (k1_wellord2 @ X20))
% 0.49/0.65          | ~ (r2_hidden @ X22 @ X20)
% 0.49/0.65          | ~ (r2_hidden @ X23 @ X20)
% 0.49/0.65          | (r1_tarski @ X22 @ X23)
% 0.49/0.65          | ~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ X21)
% 0.49/0.65          | ~ (v1_relat_1 @ X21))),
% 0.49/0.65      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.49/0.65  thf('21', plain,
% 0.49/0.65      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.49/0.65         (~ (v1_relat_1 @ (k1_wellord2 @ X20))
% 0.49/0.65          | ~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ (k1_wellord2 @ X20))
% 0.49/0.65          | (r1_tarski @ X22 @ X23)
% 0.49/0.65          | ~ (r2_hidden @ X23 @ X20)
% 0.49/0.65          | ~ (r2_hidden @ X22 @ X20))),
% 0.49/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.65  thf('22', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('23', plain,
% 0.49/0.65      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.49/0.65         (~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ (k1_wellord2 @ X20))
% 0.49/0.65          | (r1_tarski @ X22 @ X23)
% 0.49/0.65          | ~ (r2_hidden @ X23 @ X20)
% 0.49/0.65          | ~ (r2_hidden @ X22 @ X20))),
% 0.49/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.49/0.65  thf('24', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.49/0.65          | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 0.49/0.65          | (r1_tarski @ X1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['19', '23'])).
% 0.49/0.65  thf('25', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.49/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.49/0.65  thf('26', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.49/0.65          | (r1_tarski @ X1 @ X0))),
% 0.49/0.65      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.65  thf('27', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.65      inference('sup-', [status(thm)], ['5', '26'])).
% 0.49/0.65  thf('28', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.65  thf('29', plain,
% 0.49/0.65      (![X27 : $i]:
% 0.49/0.65         ((v2_wellord1 @ (k1_wellord2 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 0.49/0.65      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.49/0.65  thf(t11_wellord2, conjecture,
% 0.49/0.65    (![A:$i]:
% 0.49/0.65     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.65       ( ![B:$i]:
% 0.49/0.65         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.65           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.49/0.65             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.49/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.65    (~( ![A:$i]:
% 0.49/0.65        ( ( v3_ordinal1 @ A ) =>
% 0.49/0.65          ( ![B:$i]:
% 0.49/0.65            ( ( v3_ordinal1 @ B ) =>
% 0.49/0.65              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.49/0.65                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.49/0.65    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.49/0.65  thf('30', plain,
% 0.49/0.65      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf(t50_wellord1, axiom,
% 0.49/0.65    (![A:$i]:
% 0.49/0.65     ( ( v1_relat_1 @ A ) =>
% 0.49/0.65       ( ![B:$i]:
% 0.49/0.65         ( ( v1_relat_1 @ B ) =>
% 0.49/0.65           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.49/0.65  thf('31', plain,
% 0.49/0.65      (![X16 : $i, X17 : $i]:
% 0.49/0.65         (~ (v1_relat_1 @ X16)
% 0.49/0.65          | (r4_wellord1 @ X16 @ X17)
% 0.49/0.65          | ~ (r4_wellord1 @ X17 @ X16)
% 0.49/0.65          | ~ (v1_relat_1 @ X17))),
% 0.49/0.65      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.49/0.65  thf('32', plain,
% 0.49/0.65      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.65  thf('33', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('34', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('35', plain,
% 0.49/0.65      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.49/0.65  thf('36', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.65  thf('37', plain,
% 0.49/0.65      (![X5 : $i, X6 : $i]:
% 0.49/0.65         ((r2_hidden @ X5 @ (k1_ordinal1 @ X6)) | ~ (r2_hidden @ X5 @ X6))),
% 0.49/0.65      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.49/0.65  thf('38', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.49/0.65  thf('39', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.65  thf('40', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65             (k1_wellord2 @ (k1_ordinal1 @ X0))))),
% 0.49/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.49/0.65  thf('41', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65             (k1_wellord2 @ (k1_ordinal1 @ X0)))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.65  thf('42', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 0.49/0.65           (k1_wellord2 @ (k1_ordinal1 @ X0)))
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.65      inference('simplify', [status(thm)], ['41'])).
% 0.49/0.65  thf('43', plain,
% 0.49/0.65      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.49/0.65         (~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ (k1_wellord2 @ X20))
% 0.49/0.65          | (r1_tarski @ X22 @ X23)
% 0.49/0.65          | ~ (r2_hidden @ X23 @ X20)
% 0.49/0.65          | ~ (r2_hidden @ X22 @ X20))),
% 0.49/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.49/0.65  thf('44', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.49/0.65          | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 0.49/0.65          | (r1_tarski @ X1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.65  thf('45', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.49/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.49/0.65  thf('46', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.49/0.65          | (r1_tarski @ X1 @ X0))),
% 0.49/0.65      inference('demod', [status(thm)], ['44', '45'])).
% 0.49/0.65  thf('47', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.65      inference('sup-', [status(thm)], ['38', '46'])).
% 0.49/0.65  thf('48', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1))),
% 0.49/0.65      inference('simplify', [status(thm)], ['47'])).
% 0.49/0.65  thf(t8_wellord2, axiom,
% 0.49/0.65    (![A:$i,B:$i]:
% 0.49/0.65     ( ( r1_tarski @ A @ B ) =>
% 0.49/0.65       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.49/0.65  thf('49', plain,
% 0.49/0.65      (![X28 : $i, X29 : $i]:
% 0.49/0.65         (((k2_wellord1 @ (k1_wellord2 @ X29) @ X28) = (k1_wellord2 @ X28))
% 0.49/0.65          | ~ (r1_tarski @ X28 @ X29))),
% 0.49/0.65      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.49/0.65  thf('50', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.65  thf('51', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.65  thf('52', plain,
% 0.49/0.65      (![X25 : $i, X26 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X25)
% 0.49/0.65          | ((X26) = (k1_wellord1 @ (k1_wellord2 @ X25) @ X26))
% 0.49/0.65          | ~ (r2_hidden @ X26 @ X25)
% 0.49/0.65          | ~ (v3_ordinal1 @ X26))),
% 0.49/0.65      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.49/0.65  thf('53', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.49/0.65  thf('54', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.49/0.65          | (r1_tarski @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.65      inference('simplify', [status(thm)], ['53'])).
% 0.49/0.65  thf(t57_wellord1, axiom,
% 0.49/0.65    (![A:$i]:
% 0.49/0.65     ( ( v1_relat_1 @ A ) =>
% 0.49/0.65       ( ( v2_wellord1 @ A ) =>
% 0.49/0.65         ( ![B:$i]:
% 0.49/0.65           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.49/0.65                ( r4_wellord1 @
% 0.49/0.65                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.49/0.65  thf('55', plain,
% 0.49/0.65      (![X18 : $i, X19 : $i]:
% 0.49/0.65         (~ (v2_wellord1 @ X18)
% 0.49/0.65          | ~ (r4_wellord1 @ X18 @ 
% 0.49/0.65               (k2_wellord1 @ X18 @ (k1_wellord1 @ X18 @ X19)))
% 0.49/0.65          | ~ (r2_hidden @ X19 @ (k3_relat_1 @ X18))
% 0.49/0.65          | ~ (v1_relat_1 @ X18))),
% 0.49/0.65      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.49/0.65  thf('56', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.49/0.65             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.49/0.65          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.49/0.65  thf('57', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('58', plain,
% 0.49/0.65      (![X20 : $i, X21 : $i]:
% 0.49/0.65         (((X21) != (k1_wellord2 @ X20))
% 0.49/0.65          | ((k3_relat_1 @ X21) = (X20))
% 0.49/0.65          | ~ (v1_relat_1 @ X21))),
% 0.49/0.65      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.49/0.65  thf('59', plain,
% 0.49/0.65      (![X20 : $i]:
% 0.49/0.65         (~ (v1_relat_1 @ (k1_wellord2 @ X20))
% 0.49/0.65          | ((k3_relat_1 @ (k1_wellord2 @ X20)) = (X20)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['58'])).
% 0.49/0.65  thf('60', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('61', plain, (![X20 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X20)) = (X20))),
% 0.49/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.49/0.65  thf('62', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.49/0.65             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.49/0.65      inference('demod', [status(thm)], ['56', '57', '61'])).
% 0.49/0.65  thf('63', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.49/0.65          | ~ (r2_hidden @ X0 @ X1)
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['50', '62'])).
% 0.49/0.65  thf('64', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['63'])).
% 0.49/0.65  thf('65', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | ((sk_B) = (sk_A))
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_B)
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A)
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.49/0.65        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['35', '64'])).
% 0.49/0.65  thf('66', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('67', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('68', plain,
% 0.49/0.65      ((((sk_B) = (sk_A))
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A)
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.49/0.65        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.49/0.65  thf('69', plain, (((sk_A) != (sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('70', plain,
% 0.49/0.65      (((r1_tarski @ sk_B @ sk_A)
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.49/0.65        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.49/0.65  thf('71', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_B)
% 0.49/0.65        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A))),
% 0.49/0.65      inference('sup-', [status(thm)], ['29', '70'])).
% 0.49/0.65  thf('72', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('73', plain, ((~ (r2_hidden @ sk_A @ sk_B) | (r1_tarski @ sk_B @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.49/0.65  thf('74', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | ((sk_B) = (sk_A))
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_B)
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A)
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A))),
% 0.49/0.65      inference('sup-', [status(thm)], ['28', '73'])).
% 0.49/0.65  thf('75', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('76', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('77', plain,
% 0.49/0.65      ((((sk_B) = (sk_A))
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A)
% 0.49/0.65        | (r1_tarski @ sk_B @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.49/0.65  thf('78', plain, (((r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['77'])).
% 0.49/0.65  thf('79', plain, (((sk_A) != (sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('80', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.49/0.65  thf('81', plain,
% 0.49/0.65      (![X28 : $i, X29 : $i]:
% 0.49/0.65         (((k2_wellord1 @ (k1_wellord2 @ X29) @ X28) = (k1_wellord2 @ X28))
% 0.49/0.65          | ~ (r1_tarski @ X28 @ X29))),
% 0.49/0.65      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.49/0.65  thf('82', plain,
% 0.49/0.65      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['80', '81'])).
% 0.49/0.65  thf('83', plain,
% 0.49/0.65      (![X7 : $i, X8 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X7)
% 0.49/0.65          | (r2_hidden @ X8 @ X7)
% 0.49/0.65          | ((X8) = (X7))
% 0.49/0.65          | (r2_hidden @ X7 @ X8)
% 0.49/0.65          | ~ (v3_ordinal1 @ X8))),
% 0.49/0.65      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.49/0.65  thf('84', plain,
% 0.49/0.65      (![X25 : $i, X26 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X25)
% 0.49/0.65          | ((X26) = (k1_wellord1 @ (k1_wellord2 @ X25) @ X26))
% 0.49/0.65          | ~ (r2_hidden @ X26 @ X25)
% 0.49/0.65          | ~ (v3_ordinal1 @ X26))),
% 0.49/0.65      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.49/0.65  thf('85', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('sup-', [status(thm)], ['83', '84'])).
% 0.49/0.65  thf('86', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.65      inference('simplify', [status(thm)], ['85'])).
% 0.49/0.65  thf('87', plain,
% 0.49/0.65      (![X18 : $i, X19 : $i]:
% 0.49/0.65         (~ (v2_wellord1 @ X18)
% 0.49/0.65          | ~ (r4_wellord1 @ X18 @ 
% 0.49/0.65               (k2_wellord1 @ X18 @ (k1_wellord1 @ X18 @ X19)))
% 0.49/0.65          | ~ (r2_hidden @ X19 @ (k3_relat_1 @ X18))
% 0.49/0.65          | ~ (v1_relat_1 @ X18))),
% 0.49/0.65      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.49/0.65  thf('88', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.49/0.65             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ X1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.49/0.65          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['86', '87'])).
% 0.49/0.65  thf('89', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('90', plain, (![X20 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X20)) = (X20))),
% 0.49/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.49/0.65  thf('91', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.49/0.65             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | (r2_hidden @ X1 @ X0)
% 0.49/0.65          | ((X0) = (X1))
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ~ (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.49/0.65      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.49/0.65  thf('92', plain,
% 0.49/0.65      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | ((sk_B) = (sk_A))
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B)
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['82', '91'])).
% 0.49/0.65  thf('93', plain,
% 0.49/0.65      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('94', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('95', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('96', plain,
% 0.49/0.65      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.49/0.65        | ((sk_B) = (sk_A))
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.49/0.65  thf('97', plain, (((sk_A) != (sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('98', plain,
% 0.49/0.65      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.49/0.65  thf('99', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B)
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.49/0.65      inference('sup-', [status(thm)], ['2', '98'])).
% 0.49/0.65  thf('100', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('101', plain,
% 0.49/0.65      (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['99', '100'])).
% 0.49/0.65  thf('102', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_B)
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B)
% 0.49/0.65        | ((sk_B) = (sk_A))
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['1', '101'])).
% 0.49/0.65  thf('103', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('104', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('105', plain,
% 0.49/0.65      (((r2_hidden @ sk_A @ sk_B)
% 0.49/0.65        | ((sk_B) = (sk_A))
% 0.49/0.65        | (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.49/0.65  thf('106', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.65      inference('simplify', [status(thm)], ['105'])).
% 0.49/0.65  thf('107', plain, (((sk_A) != (sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('108', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.49/0.65  thf('109', plain,
% 0.49/0.65      (![X25 : $i, X26 : $i]:
% 0.49/0.65         (~ (v3_ordinal1 @ X25)
% 0.49/0.65          | ((X26) = (k1_wellord1 @ (k1_wellord2 @ X25) @ X26))
% 0.49/0.65          | ~ (r2_hidden @ X26 @ X25)
% 0.49/0.65          | ~ (v3_ordinal1 @ X26))),
% 0.49/0.65      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.49/0.65  thf('110', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['108', '109'])).
% 0.49/0.65  thf('111', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('112', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('113', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.49/0.65  thf('114', plain,
% 0.49/0.65      (![X18 : $i, X19 : $i]:
% 0.49/0.65         (~ (v2_wellord1 @ X18)
% 0.49/0.65          | ~ (r4_wellord1 @ X18 @ 
% 0.49/0.65               (k2_wellord1 @ X18 @ (k1_wellord1 @ X18 @ X19)))
% 0.49/0.65          | ~ (r2_hidden @ X19 @ (k3_relat_1 @ X18))
% 0.49/0.65          | ~ (v1_relat_1 @ X18))),
% 0.49/0.65      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.49/0.65  thf('115', plain,
% 0.49/0.65      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.49/0.65           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.49/0.65        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.49/0.65        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.49/0.65      inference('sup-', [status(thm)], ['113', '114'])).
% 0.49/0.65  thf('116', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         ((r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.65  thf('117', plain,
% 0.49/0.65      (![X27 : $i]:
% 0.49/0.65         ((v2_wellord1 @ (k1_wellord2 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 0.49/0.65      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.49/0.65  thf('118', plain,
% 0.49/0.65      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('119', plain,
% 0.49/0.65      (![X0 : $i, X1 : $i]:
% 0.49/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.65          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.49/0.65          | (r1_tarski @ X1 @ X0)
% 0.49/0.65          | ~ (v3_ordinal1 @ X1)
% 0.49/0.65          | ((X1) = (X0))
% 0.49/0.65          | ~ (v3_ordinal1 @ X0)
% 0.49/0.65          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['63'])).
% 0.49/0.65  thf('120', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_B)
% 0.49/0.65        | ((sk_A) = (sk_B))
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B)
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.49/0.65      inference('sup-', [status(thm)], ['118', '119'])).
% 0.49/0.65  thf('121', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('122', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('123', plain,
% 0.49/0.65      ((((sk_A) = (sk_B))
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B)
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.49/0.65  thf('124', plain, (((sk_A) != (sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('125', plain,
% 0.49/0.65      (((r1_tarski @ sk_A @ sk_B)
% 0.49/0.65        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['123', '124'])).
% 0.49/0.65  thf('126', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['117', '125'])).
% 0.49/0.65  thf('127', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('128', plain,
% 0.49/0.65      ((~ (r2_hidden @ sk_B @ sk_A) | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.65      inference('demod', [status(thm)], ['126', '127'])).
% 0.49/0.65  thf('129', plain,
% 0.49/0.65      ((~ (v3_ordinal1 @ sk_B)
% 0.49/0.65        | ((sk_A) = (sk_B))
% 0.49/0.65        | ~ (v3_ordinal1 @ sk_A)
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B)
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.65      inference('sup-', [status(thm)], ['116', '128'])).
% 0.49/0.65  thf('130', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('131', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('132', plain,
% 0.49/0.65      ((((sk_A) = (sk_B))
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B)
% 0.49/0.65        | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.65      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.49/0.65  thf('133', plain, (((r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.49/0.65      inference('simplify', [status(thm)], ['132'])).
% 0.49/0.65  thf('134', plain, (((sk_A) != (sk_B))),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('135', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 0.49/0.65  thf('136', plain,
% 0.49/0.65      (![X28 : $i, X29 : $i]:
% 0.49/0.65         (((k2_wellord1 @ (k1_wellord2 @ X29) @ X28) = (k1_wellord2 @ X28))
% 0.49/0.65          | ~ (r1_tarski @ X28 @ X29))),
% 0.49/0.65      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.49/0.65  thf('137', plain,
% 0.49/0.65      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.49/0.65      inference('sup-', [status(thm)], ['135', '136'])).
% 0.49/0.65  thf('138', plain,
% 0.49/0.65      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.49/0.65      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.49/0.65  thf('139', plain, (![X24 : $i]: (v1_relat_1 @ (k1_wellord2 @ X24))),
% 0.49/0.65      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.49/0.65  thf('140', plain,
% 0.49/0.65      (![X20 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X20)) = (X20))),
% 0.49/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.49/0.65  thf('141', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.49/0.65      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.49/0.65  thf('142', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.49/0.65      inference('demod', [status(thm)],
% 0.49/0.65                ['115', '137', '138', '139', '140', '141'])).
% 0.49/0.65  thf('143', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('sup-', [status(thm)], ['0', '142'])).
% 0.49/0.65  thf('144', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.65  thf('145', plain, ($false), inference('demod', [status(thm)], ['143', '144'])).
% 0.49/0.65  
% 0.49/0.65  % SZS output end Refutation
% 0.49/0.65  
% 0.49/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
