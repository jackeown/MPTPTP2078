%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ApgnOFhIgV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:30 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 765 expanded)
%              Number of leaves         :   27 ( 233 expanded)
%              Depth                    :   60
%              Number of atoms          : 1475 (7723 expanded)
%              Number of equality atoms :   52 ( 374 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r2_hidden @ X6 @ X5 )
      | ( X6 = X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X8 @ X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('4',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X8 @ X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

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

thf('6',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('8',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X8 @ X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X8 @ X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

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

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('17',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
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

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('25',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ sk_A @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ sk_A @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( X13 != X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_wellord1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('72',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('77',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('79',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('84',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('85',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','85','86','87'])).

thf('89',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','88'])).

thf('90',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','91'])).

thf('93',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('98',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('103',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r2_hidden @ X6 @ X5 )
      | ( X6 = X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('105',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('111',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','112'])).

thf('114',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','119'])).

thf('121',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','122'])).

thf('124',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('131',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('136',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('138',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('139',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('140',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('141',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

thf('142',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141'])).

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
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ApgnOFhIgV
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:08:51 EST 2020
% 0.22/0.36  % CPUTime    : 
% 0.22/0.36  % Running portfolio for 600 s
% 0.22/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 194 iterations in 0.165s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.46/0.64  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.46/0.64  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.46/0.64  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.46/0.64  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.46/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.64  thf(t7_wellord2, axiom,
% 0.46/0.64    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.64  thf(t24_ordinal1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.46/0.64                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X5)
% 0.46/0.64          | (r2_hidden @ X6 @ X5)
% 0.46/0.64          | ((X6) = (X5))
% 0.46/0.64          | (r2_hidden @ X5 @ X6)
% 0.46/0.64          | ~ (v3_ordinal1 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.64  thf(t26_ordinal1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X7)
% 0.46/0.64          | (r1_ordinal1 @ X8 @ X7)
% 0.46/0.64          | (r2_hidden @ X7 @ X8)
% 0.46/0.64          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X7)
% 0.46/0.64          | (r1_ordinal1 @ X8 @ X7)
% 0.46/0.64          | (r2_hidden @ X7 @ X8)
% 0.46/0.64          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.64  thf(t11_wellord2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.46/0.64             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( v3_ordinal1 @ A ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.46/0.64                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X26 : $i]:
% 0.46/0.64         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.46/0.64  thf('8', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X7)
% 0.46/0.64          | (r1_ordinal1 @ X8 @ X7)
% 0.46/0.64          | (r2_hidden @ X7 @ X8)
% 0.46/0.64          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X7)
% 0.46/0.64          | (r1_ordinal1 @ X8 @ X7)
% 0.46/0.64          | (r2_hidden @ X7 @ X8)
% 0.46/0.64          | ~ (v3_ordinal1 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.64  thf(t10_wellord2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64           ( ( r2_hidden @ A @ B ) =>
% 0.46/0.64             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X24)
% 0.46/0.64          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.64          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.64          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf(d1_wellord1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i,C:$i]:
% 0.46/0.64         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.46/0.64           ( ![D:$i]:
% 0.46/0.64             ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         (((X12) != (k1_wellord1 @ X11 @ X10))
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11)
% 0.46/0.64          | ~ (r2_hidden @ X13 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X11)
% 0.46/0.64          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X11 @ X10))
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11))),
% 0.46/0.64      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1))
% 0.46/0.64          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '15'])).
% 0.46/0.64  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.46/0.64  thf('17', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ X2))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X2 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X2)
% 0.46/0.64          | (r1_ordinal1 @ X2 @ X0)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ X2))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.64  thf(t30_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ C ) =>
% 0.46/0.64       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.46/0.64         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.46/0.64           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.46/0.64          | (r2_hidden @ X0 @ (k3_relat_1 @ X2))
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X2)
% 0.46/0.64          | ~ (v3_ordinal1 @ X2)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.46/0.64          | (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf(d1_wellord2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.46/0.64         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.64           ( ![C:$i,D:$i]:
% 0.46/0.64             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.46/0.64               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.46/0.64                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         (((X20) != (k1_wellord2 @ X19))
% 0.46/0.64          | ((k3_relat_1 @ X20) = (X19))
% 0.46/0.64          | ~ (v1_relat_1 @ X20))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X19 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.46/0.64          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.64  thf('26', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('27', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X2)
% 0.46/0.64          | ~ (v3_ordinal1 @ X2)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r2_hidden @ X2 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['22', '23', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '28'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X24)
% 0.46/0.64          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.64          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.64          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ sk_A @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         (((X12) != (k1_wellord1 @ X11 @ X10))
% 0.46/0.64          | ((X13) != (X10))
% 0.46/0.64          | ~ (r2_hidden @ X13 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X11)
% 0.46/0.64          | ~ (r2_hidden @ X10 @ (k1_wellord1 @ X11 @ X10)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '35'])).
% 0.46/0.64  thf('37', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1))),
% 0.46/0.64      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ X1 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('eq_fact', [status(thm)], ['40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['41'])).
% 0.46/0.64  thf(redefinition_r1_ordinal1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.46/0.64       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X3)
% 0.46/0.64          | ~ (v3_ordinal1 @ X4)
% 0.46/0.64          | (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_tarski @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_tarski @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.64  thf(t8_wellord2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) =>
% 0.46/0.64       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.64          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ X0) = (k1_wellord2 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf(t57_wellord1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ( v2_wellord1 @ A ) =>
% 0.46/0.64         ( ![B:$i]:
% 0.46/0.64           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.46/0.64                ( r4_wellord1 @
% 0.46/0.64                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v2_wellord1 @ X17)
% 0.46/0.64          | ~ (r4_wellord1 @ X17 @ 
% 0.46/0.64               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.46/0.64          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.46/0.64          | ~ (v1_relat_1 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.64             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('54', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.64             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['49', '55'])).
% 0.46/0.64  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ sk_A)
% 0.46/0.64          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '59'])).
% 0.46/0.64  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ sk_A @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.64        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '62'])).
% 0.46/0.64  thf('64', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      ((~ (r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.64        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '65'])).
% 0.46/0.64  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('68', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (((r1_ordinal1 @ sk_A @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.64  thf('70', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.46/0.64      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X3)
% 0.46/0.64          | ~ (v3_ordinal1 @ X4)
% 0.46/0.64          | (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (((r1_tarski @ sk_A @ sk_B)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('73', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('75', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.64      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.64          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.64             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r1_ordinal1 @ X1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.46/0.64        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.46/0.64        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t50_wellord1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v1_relat_1 @ B ) =>
% 0.46/0.64           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X15)
% 0.46/0.64          | (r4_wellord1 @ X15 @ X16)
% 0.46/0.64          | ~ (r4_wellord1 @ X16 @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('83', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('84', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('86', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('87', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.46/0.64        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.46/0.64        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['79', '85', '86', '87'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_B)
% 0.46/0.64        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.64        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '88'])).
% 0.46/0.64  thf('90', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (((r1_ordinal1 @ sk_B @ sk_A) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_B)
% 0.46/0.64        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '91'])).
% 0.46/0.64  thf('93', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('94', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (((r1_ordinal1 @ sk_B @ sk_A) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.46/0.64  thf('96', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X3)
% 0.46/0.64          | ~ (v3_ordinal1 @ X4)
% 0.46/0.64          | (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (((r1_tarski @ sk_B @ sk_A)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.64  thf('99', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('100', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('101', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.46/0.64          | ~ (r1_tarski @ X27 @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X5)
% 0.46/0.64          | (r2_hidden @ X6 @ X5)
% 0.46/0.64          | ((X6) = (X5))
% 0.46/0.64          | (r2_hidden @ X5 @ X6)
% 0.46/0.64          | ~ (v3_ordinal1 @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X24)
% 0.46/0.64          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.64          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.64          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X1)
% 0.46/0.64          | ((X1) = (X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | ((X1) = (X0))
% 0.46/0.64          | (r2_hidden @ X0 @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['106'])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v2_wellord1 @ X17)
% 0.46/0.64          | ~ (r4_wellord1 @ X17 @ 
% 0.46/0.64               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.46/0.64          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.46/0.64          | ~ (v1_relat_1 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.64             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r2_hidden @ X1 @ X0)
% 0.46/0.64          | ((X0) = (X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.64  thf('110', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.46/0.64             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r2_hidden @ X1 @ X0)
% 0.46/0.64          | ((X0) = (X1))
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.46/0.64  thf('113', plain,
% 0.46/0.64      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.46/0.64        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | ((sk_B) = (sk_A))
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B)
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['103', '112'])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('115', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('116', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.64        | ((sk_B) = (sk_A))
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.46/0.64  thf('118', plain, (((sk_A) != (sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('119', plain,
% 0.46/0.64      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.46/0.64        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B)
% 0.46/0.64        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '119'])).
% 0.46/0.64  thf('121', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['120', '121'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_B)
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B)
% 0.46/0.64        | ((sk_B) = (sk_A))
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '122'])).
% 0.46/0.64  thf('124', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('125', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_B)
% 0.46/0.64        | ((sk_B) = (sk_A))
% 0.46/0.64        | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.46/0.64  thf('127', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.64      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.64  thf('128', plain, (((sk_A) != (sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('129', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 0.46/0.64  thf('130', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X24)
% 0.46/0.64          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.46/0.64          | ~ (r2_hidden @ X25 @ X24)
% 0.46/0.64          | ~ (v3_ordinal1 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.46/0.64  thf('131', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_A)
% 0.46/0.64        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.46/0.64        | ~ (v3_ordinal1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '130'])).
% 0.46/0.64  thf('132', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('133', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('134', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v2_wellord1 @ X17)
% 0.46/0.64          | ~ (r4_wellord1 @ X17 @ 
% 0.46/0.64               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.46/0.64          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.46/0.64          | ~ (v1_relat_1 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.46/0.64           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.46/0.64        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.46/0.64        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['134', '135'])).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('138', plain,
% 0.46/0.64      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('139', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.46/0.64  thf('140', plain,
% 0.46/0.64      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('141', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 0.46/0.64  thf('142', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['136', '137', '138', '139', '140', '141'])).
% 0.46/0.64  thf('143', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '142'])).
% 0.46/0.64  thf('144', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('145', plain, ($false), inference('demod', [status(thm)], ['143', '144'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
