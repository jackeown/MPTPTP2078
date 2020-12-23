%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X0GOLRixAv

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 245 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   27
%              Number of atoms          :  872 (2459 expanded)
%              Number of equality atoms :   47 ( 142 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X21 ) @ X20 )
        = ( k1_wellord2 @ X20 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( X18
        = ( k1_wellord1 @ ( k1_wellord2 @ X17 ) @ X18 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r4_wellord1 @ X10 @ ( k2_wellord1 @ X10 @ ( k1_wellord1 @ X10 @ X11 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( v3_ordinal1 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X0 ) )
        = X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X0 ) )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_ordinal1 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

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

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13
       != ( k1_wellord2 @ X12 ) )
      | ( ( k3_relat_1 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('27',plain,(
    ! [X12: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X12 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_A = sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A = sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('49',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X19: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('58',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r4_wellord1 @ X8 @ X9 )
      | ~ ( r4_wellord1 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('62',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('63',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('65',plain,
    ( ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('75',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['56','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X0GOLRixAv
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 121 iterations in 0.066s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.51  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.51  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.51  thf(t7_wellord2, axiom,
% 0.20/0.51    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X19 : $i]:
% 0.20/0.51         ((v2_wellord1 @ (k1_wellord2 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.51  thf(t11_wellord2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.51             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.51                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.51  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X2)
% 0.20/0.51          | ~ (v3_ordinal1 @ X3)
% 0.20/0.51          | (r1_tarski @ X2 @ X3)
% 0.20/0.51          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf(t24_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.51                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X4)
% 0.20/0.51          | (r2_hidden @ X5 @ X4)
% 0.20/0.51          | ((X5) = (X4))
% 0.20/0.51          | (r2_hidden @ X4 @ X5)
% 0.20/0.51          | ~ (v3_ordinal1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.51  thf(t7_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (r1_tarski @ X7 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | (r2_hidden @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf(t8_wellord2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.51       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k1_wellord2 @ X21) @ X20) = (k1_wellord2 @ X20))
% 0.20/0.51          | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.51  thf(t10_wellord2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r2_hidden @ A @ B ) =>
% 0.20/0.51             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X17)
% 0.20/0.51          | ((X18) = (k1_wellord1 @ (k1_wellord2 @ X17) @ X18))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ X17)
% 0.20/0.51          | ~ (v3_ordinal1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf(t57_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( v2_wellord1 @ A ) =>
% 0.20/0.51         ( ![B:$i]:
% 0.20/0.51           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.51                ( r4_wellord1 @
% 0.20/0.51                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X10)
% 0.20/0.51          | ~ (r4_wellord1 @ X10 @ 
% 0.20/0.51               (k2_wellord1 @ X10 @ (k1_wellord1 @ X10 @ X11)))
% 0.20/0.51          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.51  thf('20', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X1) = (X0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ (k3_relat_1 @ (k1_wellord2 @ X0)) @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X0)) = (X1))
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.20/0.51          | ((X0) = (X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (X1))
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ X1))
% 0.20/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X0)) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.20/0.51          | (r1_ordinal1 @ (k3_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.51  thf(d1_wellord2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.51         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.51           ( ![C:$i,D:$i]:
% 0.20/0.51             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.51                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (((X13) != (k1_wellord2 @ X12))
% 0.20/0.51          | ((k3_relat_1 @ X13) = (X12))
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X12 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ X12))
% 0.20/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf('28', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('29', plain, (![X12 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, (![X12 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('31', plain, (![X12 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X12)) = (X12))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (X1))
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ X1))
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '29', '30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.20/0.51          | ((X0) = (X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((sk_A) = (sk_B))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '33'])).
% 0.20/0.51  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((((sk_A) = (sk_B))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.51  thf('38', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A)) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '39'])).
% 0.20/0.51  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X2)
% 0.20/0.51          | ~ (v3_ordinal1 @ X3)
% 0.20/0.51          | (r1_tarski @ X2 @ X3)
% 0.20/0.51          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('51', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.51  thf('53', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (r1_tarski @ X7 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('56', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X19 : $i]:
% 0.20/0.51         ((v2_wellord1 @ (k1_wellord2 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t50_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v1_relat_1 @ B ) =>
% 0.20/0.51           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X8)
% 0.20/0.51          | (r4_wellord1 @ X8 @ X9)
% 0.20/0.51          | ~ (r4_wellord1 @ X9 @ X8)
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('61', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('62', plain, (![X16 : $i]: (v1_relat_1 @ (k1_wellord2 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 0.20/0.51          | ((X0) = (X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      ((((sk_B) = (sk_A))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      ((((sk_B) = (sk_A))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.51  thf('69', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B)) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '70'])).
% 0.20/0.51  thf('72', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X2)
% 0.20/0.51          | ~ (v3_ordinal1 @ X3)
% 0.20/0.51          | (r1_tarski @ X2 @ X3)
% 0.20/0.51          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('76', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.20/0.51  thf('79', plain, ($false), inference('demod', [status(thm)], ['56', '78'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
