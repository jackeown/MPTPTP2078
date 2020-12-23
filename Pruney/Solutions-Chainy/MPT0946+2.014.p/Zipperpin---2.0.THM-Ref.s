%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KLxi9t7xS0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:29 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 238 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :   29
%              Number of atoms          :  940 (2241 expanded)
%              Number of equality atoms :   24 (  92 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
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

thf('2',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('6',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( X24
        = ( k1_wellord1 @ ( k1_wellord2 @ X23 ) @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_wellord1 @ X12 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X12 @ ( k1_wellord1 @ X12 @ X13 ) ) )
        = ( k1_wellord1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) )
      | ( r2_hidden @ X9 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_relat_1 @ X1 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
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

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
       != ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ X19 )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('18',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X18 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
        = X18 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('20',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_ordinal1 @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_ordinal1 @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X27 ) @ X26 )
        = ( k1_wellord2 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_wellord1 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ ( k2_wellord1 @ X16 @ ( k1_wellord1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k3_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('56',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X6 @ X5 )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('66',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r4_wellord1 @ X14 @ X15 )
      | ~ ( r4_wellord1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('70',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('71',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('73',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('86',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['63','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KLxi9t7xS0
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:04:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.18/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.57  % Solved by: fo/fo7.sh
% 0.18/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.57  % done 116 iterations in 0.124s
% 0.18/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.57  % SZS output start Refutation
% 0.18/0.57  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.18/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.18/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.57  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.18/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.57  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.18/0.57  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.18/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.57  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.18/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.57  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.18/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.18/0.57  thf(t26_ordinal1, axiom,
% 0.18/0.57    (![A:$i]:
% 0.18/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.18/0.57       ( ![B:$i]:
% 0.18/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.18/0.57           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.18/0.57  thf('0', plain,
% 0.18/0.57      (![X5 : $i, X6 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X5)
% 0.18/0.57          | (r1_ordinal1 @ X6 @ X5)
% 0.18/0.57          | (r2_hidden @ X5 @ X6)
% 0.18/0.57          | ~ (v3_ordinal1 @ X6))),
% 0.18/0.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.18/0.57  thf(t7_wellord2, axiom,
% 0.18/0.57    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.18/0.57  thf('1', plain,
% 0.18/0.57      (![X25 : $i]:
% 0.18/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.18/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.18/0.57  thf(t11_wellord2, conjecture,
% 0.18/0.57    (![A:$i]:
% 0.18/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.18/0.57       ( ![B:$i]:
% 0.18/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.18/0.57           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.18/0.57             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.18/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.57    (~( ![A:$i]:
% 0.18/0.57        ( ( v3_ordinal1 @ A ) =>
% 0.18/0.57          ( ![B:$i]:
% 0.18/0.57            ( ( v3_ordinal1 @ B ) =>
% 0.18/0.57              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.18/0.57                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.18/0.57    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.18/0.57  thf('2', plain,
% 0.18/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf(d10_xboole_0, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.57  thf('3', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.18/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.57  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.18/0.57      inference('simplify', [status(thm)], ['3'])).
% 0.18/0.57  thf('5', plain,
% 0.18/0.57      (![X5 : $i, X6 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X5)
% 0.18/0.57          | (r1_ordinal1 @ X6 @ X5)
% 0.18/0.57          | (r2_hidden @ X5 @ X6)
% 0.18/0.57          | ~ (v3_ordinal1 @ X6))),
% 0.18/0.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.18/0.57  thf('6', plain,
% 0.18/0.57      (![X25 : $i]:
% 0.18/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.18/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.18/0.57  thf('7', plain,
% 0.18/0.57      (![X5 : $i, X6 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X5)
% 0.18/0.57          | (r1_ordinal1 @ X6 @ X5)
% 0.18/0.57          | (r2_hidden @ X5 @ X6)
% 0.18/0.57          | ~ (v3_ordinal1 @ X6))),
% 0.18/0.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.18/0.57  thf(t10_wellord2, axiom,
% 0.18/0.57    (![A:$i]:
% 0.18/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.18/0.57       ( ![B:$i]:
% 0.18/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.18/0.57           ( ( r2_hidden @ A @ B ) =>
% 0.18/0.57             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.18/0.57  thf('8', plain,
% 0.18/0.57      (![X23 : $i, X24 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X23)
% 0.18/0.57          | ((X24) = (k1_wellord1 @ (k1_wellord2 @ X23) @ X24))
% 0.18/0.57          | ~ (r2_hidden @ X24 @ X23)
% 0.18/0.57          | ~ (v3_ordinal1 @ X24))),
% 0.18/0.57      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.18/0.57  thf('9', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.18/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.57  thf('10', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.18/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.18/0.57  thf(t40_wellord1, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( v1_relat_1 @ B ) =>
% 0.18/0.57       ( ( v2_wellord1 @ B ) =>
% 0.18/0.57         ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) ) =
% 0.18/0.57           ( k1_wellord1 @ B @ A ) ) ) ))).
% 0.18/0.57  thf('11', plain,
% 0.18/0.57      (![X12 : $i, X13 : $i]:
% 0.18/0.57         (~ (v2_wellord1 @ X12)
% 0.18/0.57          | ((k3_relat_1 @ (k2_wellord1 @ X12 @ (k1_wellord1 @ X12 @ X13)))
% 0.18/0.57              = (k1_wellord1 @ X12 @ X13))
% 0.18/0.57          | ~ (v1_relat_1 @ X12))),
% 0.18/0.57      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.18/0.57  thf(t19_wellord1, axiom,
% 0.18/0.57    (![A:$i,B:$i,C:$i]:
% 0.18/0.57     ( ( v1_relat_1 @ C ) =>
% 0.18/0.57       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 0.18/0.57         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 0.18/0.57  thf('12', plain,
% 0.18/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X9 @ (k3_relat_1 @ (k2_wellord1 @ X10 @ X11)))
% 0.18/0.57          | (r2_hidden @ X9 @ (k3_relat_1 @ X10))
% 0.18/0.57          | ~ (v1_relat_1 @ X10))),
% 0.18/0.57      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.18/0.57  thf('13', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X2 @ (k1_wellord1 @ X1 @ X0))
% 0.18/0.57          | ~ (v1_relat_1 @ X1)
% 0.18/0.57          | ~ (v2_wellord1 @ X1)
% 0.18/0.57          | ~ (v1_relat_1 @ X1)
% 0.18/0.57          | (r2_hidden @ X2 @ (k3_relat_1 @ X1)))),
% 0.18/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.57  thf('14', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         ((r2_hidden @ X2 @ (k3_relat_1 @ X1))
% 0.18/0.57          | ~ (v2_wellord1 @ X1)
% 0.18/0.57          | ~ (v1_relat_1 @ X1)
% 0.18/0.57          | ~ (r2_hidden @ X2 @ (k1_wellord1 @ X1 @ X0)))),
% 0.18/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.18/0.57  thf('15', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X2 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X1))))),
% 0.18/0.57      inference('sup-', [status(thm)], ['10', '14'])).
% 0.18/0.57  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.18/0.57  thf('16', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.18/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.18/0.57  thf(d1_wellord2, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( v1_relat_1 @ B ) =>
% 0.18/0.57       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.18/0.57         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.18/0.57           ( ![C:$i,D:$i]:
% 0.18/0.57             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.18/0.57               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.18/0.57                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.18/0.57  thf('17', plain,
% 0.18/0.57      (![X18 : $i, X19 : $i]:
% 0.18/0.57         (((X19) != (k1_wellord2 @ X18))
% 0.18/0.57          | ((k3_relat_1 @ X19) = (X18))
% 0.18/0.57          | ~ (v1_relat_1 @ X19))),
% 0.18/0.57      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.18/0.57  thf('18', plain,
% 0.18/0.57      (![X18 : $i]:
% 0.18/0.57         (~ (v1_relat_1 @ (k1_wellord2 @ X18))
% 0.18/0.57          | ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18)))),
% 0.18/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.18/0.57  thf('19', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.18/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.18/0.57  thf('20', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.18/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.18/0.57  thf('21', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X2 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | (r2_hidden @ X2 @ X1))),
% 0.18/0.57      inference('demod', [status(thm)], ['15', '16', '20'])).
% 0.18/0.57  thf('22', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r2_hidden @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X2)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X2)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (r2_hidden @ X1 @ X2))),
% 0.18/0.57      inference('sup-', [status(thm)], ['6', '21'])).
% 0.18/0.57  thf('23', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X1 @ X2)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X2)
% 0.18/0.57          | ~ (v3_ordinal1 @ X2)
% 0.18/0.57          | (r2_hidden @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.18/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.18/0.57  thf('24', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X2)
% 0.18/0.57          | (r2_hidden @ X1 @ X2)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X2 @ X0))),
% 0.18/0.57      inference('sup-', [status(thm)], ['5', '23'])).
% 0.18/0.57  thf('25', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         ((r1_ordinal1 @ X2 @ X0)
% 0.18/0.57          | (r2_hidden @ X1 @ X2)
% 0.18/0.57          | ~ (v3_ordinal1 @ X2)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.18/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.18/0.57  thf(t7_ordinal1, axiom,
% 0.18/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.57  thf('26', plain,
% 0.18/0.57      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.18/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.18/0.57  thf('27', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X2)
% 0.18/0.57          | (r1_ordinal1 @ X2 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X2)
% 0.18/0.57          | ~ (r1_tarski @ X0 @ X1))),
% 0.18/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.18/0.57  thf('28', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.18/0.57      inference('sup-', [status(thm)], ['4', '27'])).
% 0.18/0.57  thf('29', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1))),
% 0.18/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.18/0.57  thf(redefinition_r1_ordinal1, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.18/0.57       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.18/0.57  thf('30', plain,
% 0.18/0.57      (![X3 : $i, X4 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X3)
% 0.18/0.57          | ~ (v3_ordinal1 @ X4)
% 0.18/0.57          | (r1_tarski @ X3 @ X4)
% 0.18/0.57          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.18/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.18/0.57  thf('31', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_tarski @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.18/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.57  thf('32', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((r1_tarski @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1))),
% 0.18/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.18/0.57  thf(t8_wellord2, axiom,
% 0.18/0.57    (![A:$i,B:$i]:
% 0.18/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.18/0.57       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.18/0.57  thf('33', plain,
% 0.18/0.57      (![X26 : $i, X27 : $i]:
% 0.18/0.57         (((k2_wellord1 @ (k1_wellord2 @ X27) @ X26) = (k1_wellord2 @ X26))
% 0.18/0.57          | ~ (r1_tarski @ X26 @ X27))),
% 0.18/0.57      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.18/0.57  thf('34', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         ((r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.18/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.18/0.57  thf('35', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0))),
% 0.18/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.18/0.57  thf(t57_wellord1, axiom,
% 0.18/0.57    (![A:$i]:
% 0.18/0.57     ( ( v1_relat_1 @ A ) =>
% 0.18/0.57       ( ( v2_wellord1 @ A ) =>
% 0.18/0.57         ( ![B:$i]:
% 0.18/0.57           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.18/0.57                ( r4_wellord1 @
% 0.18/0.57                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.18/0.57  thf('36', plain,
% 0.18/0.57      (![X16 : $i, X17 : $i]:
% 0.18/0.57         (~ (v2_wellord1 @ X16)
% 0.18/0.57          | ~ (r4_wellord1 @ X16 @ 
% 0.18/0.57               (k2_wellord1 @ X16 @ (k1_wellord1 @ X16 @ X17)))
% 0.18/0.57          | ~ (r2_hidden @ X17 @ (k3_relat_1 @ X16))
% 0.18/0.57          | ~ (v1_relat_1 @ X16))),
% 0.18/0.57      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.18/0.57  thf('37', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.18/0.57             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.18/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.18/0.57  thf('38', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.18/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.18/0.57  thf('39', plain, (![X18 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X18)) = (X18))),
% 0.18/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.18/0.57  thf('40', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.18/0.57             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.18/0.57      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.18/0.57  thf('41', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | ~ (r2_hidden @ X0 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1))),
% 0.18/0.57      inference('sup-', [status(thm)], ['34', '40'])).
% 0.18/0.57  thf('42', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.18/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.18/0.57  thf('43', plain,
% 0.18/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.18/0.57        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.18/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.18/0.57        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['2', '42'])).
% 0.18/0.57  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('46', plain,
% 0.18/0.57      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.18/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.18/0.57        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.18/0.57      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.18/0.57  thf('47', plain,
% 0.18/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.18/0.57        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.18/0.57        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.18/0.57      inference('sup-', [status(thm)], ['1', '46'])).
% 0.18/0.57  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('49', plain,
% 0.18/0.57      ((~ (r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.18/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.18/0.57  thf('50', plain,
% 0.18/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.18/0.57        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_B)
% 0.18/0.57        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.18/0.57      inference('sup-', [status(thm)], ['0', '49'])).
% 0.18/0.57  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('52', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('53', plain,
% 0.18/0.57      (((r1_ordinal1 @ sk_A @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.18/0.57      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.18/0.57  thf('54', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.18/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.18/0.57  thf('55', plain,
% 0.18/0.57      (![X3 : $i, X4 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X3)
% 0.18/0.57          | ~ (v3_ordinal1 @ X4)
% 0.18/0.57          | (r1_tarski @ X3 @ X4)
% 0.18/0.57          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.18/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.18/0.57  thf('56', plain,
% 0.18/0.57      (((r1_tarski @ sk_A @ sk_B)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_B)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.18/0.57  thf('57', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('59', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.18/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.18/0.57  thf('60', plain,
% 0.18/0.57      (![X0 : $i, X2 : $i]:
% 0.18/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.57  thf('61', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.18/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.18/0.57  thf('62', plain, (((sk_A) != (sk_B))),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('63', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.18/0.57      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.18/0.57  thf('64', plain,
% 0.18/0.57      (![X5 : $i, X6 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X5)
% 0.18/0.57          | (r1_ordinal1 @ X6 @ X5)
% 0.18/0.57          | (r2_hidden @ X5 @ X6)
% 0.18/0.57          | ~ (v3_ordinal1 @ X6))),
% 0.18/0.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.18/0.57  thf('65', plain,
% 0.18/0.57      (![X25 : $i]:
% 0.18/0.57         ((v2_wellord1 @ (k1_wellord2 @ X25)) | ~ (v3_ordinal1 @ X25))),
% 0.18/0.57      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.18/0.57  thf('66', plain,
% 0.18/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf(t50_wellord1, axiom,
% 0.18/0.57    (![A:$i]:
% 0.18/0.57     ( ( v1_relat_1 @ A ) =>
% 0.18/0.57       ( ![B:$i]:
% 0.18/0.57         ( ( v1_relat_1 @ B ) =>
% 0.18/0.57           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.18/0.57  thf('67', plain,
% 0.18/0.57      (![X14 : $i, X15 : $i]:
% 0.18/0.57         (~ (v1_relat_1 @ X14)
% 0.18/0.57          | (r4_wellord1 @ X14 @ X15)
% 0.18/0.57          | ~ (r4_wellord1 @ X15 @ X14)
% 0.18/0.57          | ~ (v1_relat_1 @ X15))),
% 0.18/0.57      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.18/0.57  thf('68', plain,
% 0.18/0.57      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.18/0.57        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.18/0.57        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.18/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.18/0.57  thf('69', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.18/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.18/0.57  thf('70', plain, (![X22 : $i]: (v1_relat_1 @ (k1_wellord2 @ X22))),
% 0.18/0.57      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.18/0.57  thf('71', plain,
% 0.18/0.57      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.18/0.57      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.18/0.57  thf('72', plain,
% 0.18/0.57      (![X0 : $i, X1 : $i]:
% 0.18/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.57          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.18/0.57          | (r1_ordinal1 @ X1 @ X0)
% 0.18/0.57          | ~ (v3_ordinal1 @ X1)
% 0.18/0.57          | ~ (v3_ordinal1 @ X0)
% 0.18/0.57          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.18/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.18/0.57  thf('73', plain,
% 0.18/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_B)
% 0.18/0.57        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.18/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.18/0.57        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.18/0.57      inference('sup-', [status(thm)], ['71', '72'])).
% 0.18/0.57  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('75', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('76', plain,
% 0.18/0.57      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.18/0.57        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.18/0.57        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.18/0.57      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.18/0.57  thf('77', plain,
% 0.18/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.18/0.57        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.18/0.57        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['65', '76'])).
% 0.18/0.57  thf('78', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('79', plain,
% 0.18/0.57      ((~ (r2_hidden @ sk_A @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.18/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.18/0.57  thf('80', plain,
% 0.18/0.57      ((~ (v3_ordinal1 @ sk_B)
% 0.18/0.57        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.18/0.57        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.18/0.57      inference('sup-', [status(thm)], ['64', '79'])).
% 0.18/0.57  thf('81', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('82', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('83', plain,
% 0.18/0.57      (((r1_ordinal1 @ sk_B @ sk_A) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.18/0.57      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.18/0.57  thf('84', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.18/0.57      inference('simplify', [status(thm)], ['83'])).
% 0.18/0.57  thf('85', plain,
% 0.18/0.57      (![X3 : $i, X4 : $i]:
% 0.18/0.57         (~ (v3_ordinal1 @ X3)
% 0.18/0.57          | ~ (v3_ordinal1 @ X4)
% 0.18/0.57          | (r1_tarski @ X3 @ X4)
% 0.18/0.57          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.18/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.18/0.57  thf('86', plain,
% 0.18/0.57      (((r1_tarski @ sk_B @ sk_A)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_A)
% 0.18/0.57        | ~ (v3_ordinal1 @ sk_B))),
% 0.18/0.57      inference('sup-', [status(thm)], ['84', '85'])).
% 0.18/0.57  thf('87', plain, ((v3_ordinal1 @ sk_A)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('88', plain, ((v3_ordinal1 @ sk_B)),
% 0.18/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.57  thf('89', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.18/0.57      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.18/0.57  thf('90', plain, ($false), inference('demod', [status(thm)], ['63', '89'])).
% 0.18/0.57  
% 0.18/0.57  % SZS output end Refutation
% 0.18/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
