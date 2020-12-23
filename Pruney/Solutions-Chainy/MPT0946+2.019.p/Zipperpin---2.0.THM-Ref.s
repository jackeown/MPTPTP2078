%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNTJxbTCvp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 895 expanded)
%              Number of leaves         :   28 ( 270 expanded)
%              Depth                    :   62
%              Number of atoms          : 1573 (9183 expanded)
%              Number of equality atoms :   59 ( 451 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ X3 @ X2 )
      | ( X3 = X2 )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X28 ) )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('3',plain,(
    ! [X28: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X28 ) )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
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

thf('5',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X28: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X28 ) )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X5 @ X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( X27
        = ( k1_wellord1 @ ( k1_wellord2 @ X26 ) @ X27 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X28: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X28 ) )
      | ~ ( v3_ordinal1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_wellord1 @ X15 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X15 @ ( k1_wellord1 @ X15 @ X16 ) ) )
        = ( k1_wellord1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
        = ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('17',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
        = ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ X12 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( X22
       != ( k1_wellord2 @ X21 ) )
      | ( ( k3_relat_1 @ X22 )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('25',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X21 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
        = X21 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('27',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X2 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( X27
        = ( k1_wellord1 @ ( k1_wellord2 @ X26 ) @ X27 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ sk_A @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( r1_ordinal1 @ sk_A @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

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

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k1_wellord1 @ X8 @ X7 ) )
      | ( X10 != X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ sk_A )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('52',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X30 ) @ X29 )
        = ( k1_wellord2 @ X29 ) )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ~ ( r4_wellord1 @ X19 @ ( k2_wellord1 @ X19 @ ( k1_wellord1 @ X19 @ X20 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k3_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','66'])).

thf('68',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','69'])).

thf('71',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('76',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X30 ) @ X29 )
        = ( k1_wellord2 @ X29 ) )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('81',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('83',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('85',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r4_wellord1 @ X17 @ X18 )
      | ~ ( r4_wellord1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('88',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('89',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['83','89','90','91'])).

thf('93',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','92'])).

thf('94',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','95'])).

thf('97',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('102',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X30 ) @ X29 )
        = ( k1_wellord2 @ X29 ) )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('107',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ X3 @ X2 )
      | ( X3 = X2 )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('109',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( X27
        = ( k1_wellord1 @ ( k1_wellord2 @ X26 ) @ X27 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ~ ( r4_wellord1 @ X19 @ ( k2_wellord1 @ X19 @ ( k1_wellord1 @ X19 @ X20 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k3_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('115',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','123'])).

thf('125',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','126'])).

thf('128',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( X27
        = ( k1_wellord1 @ ( k1_wellord2 @ X26 ) @ X27 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('135',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('140',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_A )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('142',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('143',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ X12 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('146',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('147',plain,(
    ! [X21: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['141','148'])).

thf('150',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['140','149','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNTJxbTCvp
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.62  % Solved by: fo/fo7.sh
% 0.20/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.62  % done 194 iterations in 0.184s
% 0.20/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.62  % SZS output start Refutation
% 0.20/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.62  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.62  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.62  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.62  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.62  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.62  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.62  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.62  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.62  thf(t24_ordinal1, axiom,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.62       ( ![B:$i]:
% 0.20/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.62           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.62                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.62  thf('0', plain,
% 0.20/0.62      (![X2 : $i, X3 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X2)
% 0.20/0.62          | (r2_hidden @ X3 @ X2)
% 0.20/0.62          | ((X3) = (X2))
% 0.20/0.62          | (r2_hidden @ X2 @ X3)
% 0.20/0.62          | ~ (v3_ordinal1 @ X3))),
% 0.20/0.62      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.62  thf(t7_wellord2, axiom,
% 0.20/0.62    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.20/0.62  thf('1', plain,
% 0.20/0.62      (![X28 : $i]:
% 0.20/0.62         ((v2_wellord1 @ (k1_wellord2 @ X28)) | ~ (v3_ordinal1 @ X28))),
% 0.20/0.62      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.62  thf(t26_ordinal1, axiom,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.62       ( ![B:$i]:
% 0.20/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.62           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.62  thf('2', plain,
% 0.20/0.62      (![X4 : $i, X5 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X4)
% 0.20/0.62          | (r1_ordinal1 @ X5 @ X4)
% 0.20/0.62          | (r2_hidden @ X4 @ X5)
% 0.20/0.62          | ~ (v3_ordinal1 @ X5))),
% 0.20/0.62      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.62  thf('3', plain,
% 0.20/0.62      (![X28 : $i]:
% 0.20/0.62         ((v2_wellord1 @ (k1_wellord2 @ X28)) | ~ (v3_ordinal1 @ X28))),
% 0.20/0.62      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.62  thf('4', plain,
% 0.20/0.62      (![X4 : $i, X5 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X4)
% 0.20/0.62          | (r1_ordinal1 @ X5 @ X4)
% 0.20/0.62          | (r2_hidden @ X4 @ X5)
% 0.20/0.62          | ~ (v3_ordinal1 @ X5))),
% 0.20/0.62      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.62  thf(t11_wellord2, conjecture,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.62       ( ![B:$i]:
% 0.20/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.62           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.62             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.62    (~( ![A:$i]:
% 0.20/0.62        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.62          ( ![B:$i]:
% 0.20/0.62            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.62              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.62                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.62    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.20/0.62  thf('5', plain,
% 0.20/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('6', plain,
% 0.20/0.62      (![X28 : $i]:
% 0.20/0.62         ((v2_wellord1 @ (k1_wellord2 @ X28)) | ~ (v3_ordinal1 @ X28))),
% 0.20/0.62      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.62  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('8', plain,
% 0.20/0.62      (![X4 : $i, X5 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X4)
% 0.20/0.62          | (r1_ordinal1 @ X5 @ X4)
% 0.20/0.62          | (r2_hidden @ X4 @ X5)
% 0.20/0.62          | ~ (v3_ordinal1 @ X5))),
% 0.20/0.62      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.62  thf('9', plain,
% 0.20/0.62      (![X4 : $i, X5 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X4)
% 0.20/0.62          | (r1_ordinal1 @ X5 @ X4)
% 0.20/0.62          | (r2_hidden @ X4 @ X5)
% 0.20/0.62          | ~ (v3_ordinal1 @ X5))),
% 0.20/0.62      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.62  thf(t10_wellord2, axiom,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.62       ( ![B:$i]:
% 0.20/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.62           ( ( r2_hidden @ A @ B ) =>
% 0.20/0.62             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.62  thf('10', plain,
% 0.20/0.62      (![X26 : $i, X27 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X26)
% 0.20/0.62          | ((X27) = (k1_wellord1 @ (k1_wellord2 @ X26) @ X27))
% 0.20/0.62          | ~ (r2_hidden @ X27 @ X26)
% 0.20/0.62          | ~ (v3_ordinal1 @ X27))),
% 0.20/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.62  thf('11', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.62  thf('12', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.62  thf('13', plain,
% 0.20/0.62      (![X28 : $i]:
% 0.20/0.62         ((v2_wellord1 @ (k1_wellord2 @ X28)) | ~ (v3_ordinal1 @ X28))),
% 0.20/0.62      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.62  thf('14', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.62  thf(t40_wellord1, axiom,
% 0.20/0.62    (![A:$i,B:$i]:
% 0.20/0.62     ( ( v1_relat_1 @ B ) =>
% 0.20/0.62       ( ( v2_wellord1 @ B ) =>
% 0.20/0.62         ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) ) =
% 0.20/0.62           ( k1_wellord1 @ B @ A ) ) ) ))).
% 0.20/0.62  thf('15', plain,
% 0.20/0.62      (![X15 : $i, X16 : $i]:
% 0.20/0.62         (~ (v2_wellord1 @ X15)
% 0.20/0.62          | ((k3_relat_1 @ (k2_wellord1 @ X15 @ (k1_wellord1 @ X15 @ X16)))
% 0.20/0.62              = (k1_wellord1 @ X15 @ X16))
% 0.20/0.62          | ~ (v1_relat_1 @ X15))),
% 0.20/0.62      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.20/0.62  thf('16', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((k3_relat_1 @ (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62            = (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.62  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.62  thf('17', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('18', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((k3_relat_1 @ (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62            = (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.62  thf('19', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ((k3_relat_1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62              = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['13', '18'])).
% 0.20/0.62  thf('20', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((k3_relat_1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62            = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.62  thf(t19_wellord1, axiom,
% 0.20/0.62    (![A:$i,B:$i,C:$i]:
% 0.20/0.62     ( ( v1_relat_1 @ C ) =>
% 0.20/0.62       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 0.20/0.62         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 0.20/0.62  thf('21', plain,
% 0.20/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X12 @ (k3_relat_1 @ (k2_wellord1 @ X13 @ X14)))
% 0.20/0.62          | (r2_hidden @ X12 @ (k3_relat_1 @ X13))
% 0.20/0.62          | ~ (v1_relat_1 @ X13))),
% 0.20/0.62      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.20/0.62  thf('22', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.62          | (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X1))))),
% 0.20/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.62  thf('23', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf(d1_wellord2, axiom,
% 0.20/0.62    (![A:$i,B:$i]:
% 0.20/0.62     ( ( v1_relat_1 @ B ) =>
% 0.20/0.62       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.62         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.62           ( ![C:$i,D:$i]:
% 0.20/0.62             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.62               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.62                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.62  thf('24', plain,
% 0.20/0.62      (![X21 : $i, X22 : $i]:
% 0.20/0.62         (((X22) != (k1_wellord2 @ X21))
% 0.20/0.62          | ((k3_relat_1 @ X22) = (X21))
% 0.20/0.62          | ~ (v1_relat_1 @ X22))),
% 0.20/0.62      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.62  thf('25', plain,
% 0.20/0.62      (![X21 : $i]:
% 0.20/0.62         (~ (v1_relat_1 @ (k1_wellord2 @ X21))
% 0.20/0.62          | ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21)))),
% 0.20/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.62  thf('26', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('27', plain, (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.20/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.62  thf('28', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | (r2_hidden @ X2 @ X1))),
% 0.20/0.62      inference('demod', [status(thm)], ['22', '23', '27'])).
% 0.20/0.62  thf('29', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r2_hidden @ X2 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.62      inference('sup-', [status(thm)], ['12', '28'])).
% 0.20/0.62  thf('30', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.62         ((r2_hidden @ X2 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (r2_hidden @ X2 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.62  thf('31', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X2)
% 0.20/0.62          | (r1_ordinal1 @ X2 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r2_hidden @ X1 @ X2))),
% 0.20/0.62      inference('sup-', [status(thm)], ['8', '30'])).
% 0.20/0.62  thf('32', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.62         ((r2_hidden @ X1 @ X2)
% 0.20/0.62          | (r1_ordinal1 @ X2 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X2)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.62  thf('33', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ sk_A)
% 0.20/0.62          | (r2_hidden @ X0 @ X1))),
% 0.20/0.62      inference('sup-', [status(thm)], ['7', '32'])).
% 0.20/0.62  thf('34', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ sk_A)
% 0.20/0.62          | (r2_hidden @ X0 @ X1))),
% 0.20/0.62      inference('sup-', [status(thm)], ['7', '32'])).
% 0.20/0.62  thf('35', plain,
% 0.20/0.62      (![X26 : $i, X27 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X26)
% 0.20/0.62          | ((X27) = (k1_wellord1 @ (k1_wellord2 @ X26) @ X27))
% 0.20/0.62          | ~ (r2_hidden @ X27 @ X26)
% 0.20/0.62          | ~ (v3_ordinal1 @ X27))),
% 0.20/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.62  thf('36', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.62  thf('37', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.20/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.62  thf(d1_wellord1, axiom,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v1_relat_1 @ A ) =>
% 0.20/0.62       ( ![B:$i,C:$i]:
% 0.20/0.62         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.20/0.62           ( ![D:$i]:
% 0.20/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.62               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.20/0.62  thf('38', plain,
% 0.20/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.62         (((X9) != (k1_wellord1 @ X8 @ X7))
% 0.20/0.62          | ((X10) != (X7))
% 0.20/0.62          | ~ (r2_hidden @ X10 @ X9)
% 0.20/0.62          | ~ (v1_relat_1 @ X8))),
% 0.20/0.62      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.62  thf('39', plain,
% 0.20/0.62      (![X7 : $i, X8 : $i]:
% 0.20/0.62         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 0.20/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.62  thf('40', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X0 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.62  thf('41', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('42', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X0 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0))),
% 0.20/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.62  thf('43', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.62  thf('44', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ X1 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.20/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.62  thf('45', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('eq_fact', [status(thm)], ['44'])).
% 0.20/0.62  thf('46', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         ((r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.20/0.62      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.62  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.62    (![A:$i,B:$i]:
% 0.20/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.62       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.62  thf('47', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_tarski @ X0 @ X1)
% 0.20/0.62          | ~ (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.62  thf('48', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.62  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('50', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.62  thf('51', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         ((r1_tarski @ X0 @ sk_A)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.62  thf(t8_wellord2, axiom,
% 0.20/0.62    (![A:$i,B:$i]:
% 0.20/0.62     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.62       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.20/0.62  thf('52', plain,
% 0.20/0.62      (![X29 : $i, X30 : $i]:
% 0.20/0.62         (((k2_wellord1 @ (k1_wellord2 @ X30) @ X29) = (k1_wellord2 @ X29))
% 0.20/0.62          | ~ (r1_tarski @ X29 @ X30))),
% 0.20/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.62  thf('53', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ X0) = (k1_wellord2 @ X0)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.62  thf('54', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.62  thf(t57_wellord1, axiom,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v1_relat_1 @ A ) =>
% 0.20/0.62       ( ( v2_wellord1 @ A ) =>
% 0.20/0.62         ( ![B:$i]:
% 0.20/0.62           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.62                ( r4_wellord1 @
% 0.20/0.62                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.62  thf('55', plain,
% 0.20/0.62      (![X19 : $i, X20 : $i]:
% 0.20/0.62         (~ (v2_wellord1 @ X19)
% 0.20/0.62          | ~ (r4_wellord1 @ X19 @ 
% 0.20/0.62               (k2_wellord1 @ X19 @ (k1_wellord1 @ X19 @ X20)))
% 0.20/0.62          | ~ (r2_hidden @ X20 @ (k3_relat_1 @ X19))
% 0.20/0.62          | ~ (v1_relat_1 @ X19))),
% 0.20/0.62      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.62  thf('56', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.62          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.62  thf('57', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('58', plain, (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.20/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.62  thf('59', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.62  thf('60', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62          | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['53', '59'])).
% 0.20/0.62  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('62', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62          | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0))),
% 0.20/0.62      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.62  thf('63', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0)))),
% 0.20/0.62      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.62  thf('64', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ sk_A)
% 0.20/0.62          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['6', '63'])).
% 0.20/0.62  thf('65', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('66', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ X0))
% 0.20/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.62  thf('67', plain,
% 0.20/0.62      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.62        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['5', '66'])).
% 0.20/0.62  thf('68', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('69', plain,
% 0.20/0.62      ((~ (r2_hidden @ sk_B @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.62      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.62  thf('70', plain,
% 0.20/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.62        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['4', '69'])).
% 0.20/0.62  thf('71', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('72', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('73', plain,
% 0.20/0.62      (((r1_ordinal1 @ sk_A @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.62      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.62  thf('74', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.62      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.62  thf('75', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_tarski @ X0 @ X1)
% 0.20/0.62          | ~ (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.62  thf('76', plain,
% 0.20/0.62      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.62  thf('77', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('78', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('79', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.62      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.20/0.62  thf('80', plain,
% 0.20/0.62      (![X29 : $i, X30 : $i]:
% 0.20/0.62         (((k2_wellord1 @ (k1_wellord2 @ X30) @ X29) = (k1_wellord2 @ X29))
% 0.20/0.62          | ~ (r1_tarski @ X29 @ X30))),
% 0.20/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.62  thf('81', plain,
% 0.20/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.62  thf('82', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.62  thf('83', plain,
% 0.20/0.62      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.62        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.62  thf('84', plain,
% 0.20/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf(t50_wellord1, axiom,
% 0.20/0.62    (![A:$i]:
% 0.20/0.62     ( ( v1_relat_1 @ A ) =>
% 0.20/0.62       ( ![B:$i]:
% 0.20/0.62         ( ( v1_relat_1 @ B ) =>
% 0.20/0.62           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.20/0.62  thf('85', plain,
% 0.20/0.62      (![X17 : $i, X18 : $i]:
% 0.20/0.62         (~ (v1_relat_1 @ X17)
% 0.20/0.62          | (r4_wellord1 @ X17 @ X18)
% 0.20/0.62          | ~ (r4_wellord1 @ X18 @ X17)
% 0.20/0.62          | ~ (v1_relat_1 @ X18))),
% 0.20/0.62      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.20/0.62  thf('86', plain,
% 0.20/0.62      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.62        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.62  thf('87', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('88', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('89', plain,
% 0.20/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.20/0.62  thf('90', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('91', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('92', plain,
% 0.20/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.62        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.62        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['83', '89', '90', '91'])).
% 0.20/0.62  thf('93', plain,
% 0.20/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.62        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.62        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['3', '92'])).
% 0.20/0.62  thf('94', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('95', plain,
% 0.20/0.62      (((r1_ordinal1 @ sk_B @ sk_A) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.62  thf('96', plain,
% 0.20/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.62        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['2', '95'])).
% 0.20/0.62  thf('97', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('98', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('99', plain,
% 0.20/0.62      (((r1_ordinal1 @ sk_B @ sk_A) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.62  thf('100', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.20/0.62      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.62  thf('101', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r1_tarski @ X0 @ X1)
% 0.20/0.62          | ~ (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.62  thf('102', plain,
% 0.20/0.62      (((r1_tarski @ sk_B @ sk_A)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.62  thf('103', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('104', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('105', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.62      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.20/0.62  thf('106', plain,
% 0.20/0.62      (![X29 : $i, X30 : $i]:
% 0.20/0.62         (((k2_wellord1 @ (k1_wellord2 @ X30) @ X29) = (k1_wellord2 @ X29))
% 0.20/0.62          | ~ (r1_tarski @ X29 @ X30))),
% 0.20/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.62  thf('107', plain,
% 0.20/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.62  thf('108', plain,
% 0.20/0.62      (![X2 : $i, X3 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X2)
% 0.20/0.62          | (r2_hidden @ X3 @ X2)
% 0.20/0.62          | ((X3) = (X2))
% 0.20/0.62          | (r2_hidden @ X2 @ X3)
% 0.20/0.62          | ~ (v3_ordinal1 @ X3))),
% 0.20/0.62      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.62  thf('109', plain,
% 0.20/0.62      (![X26 : $i, X27 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X26)
% 0.20/0.62          | ((X27) = (k1_wellord1 @ (k1_wellord2 @ X26) @ X27))
% 0.20/0.62          | ~ (r2_hidden @ X27 @ X26)
% 0.20/0.62          | ~ (v3_ordinal1 @ X27))),
% 0.20/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.62  thf('110', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X1)
% 0.20/0.62          | (r2_hidden @ X0 @ X1)
% 0.20/0.62          | ((X1) = (X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.62      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.62  thf('111', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | ((X1) = (X0))
% 0.20/0.62          | (r2_hidden @ X0 @ X1)
% 0.20/0.62          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.62      inference('simplify', [status(thm)], ['110'])).
% 0.20/0.62  thf('112', plain,
% 0.20/0.62      (![X19 : $i, X20 : $i]:
% 0.20/0.62         (~ (v2_wellord1 @ X19)
% 0.20/0.62          | ~ (r4_wellord1 @ X19 @ 
% 0.20/0.62               (k2_wellord1 @ X19 @ (k1_wellord1 @ X19 @ X20)))
% 0.20/0.62          | ~ (r2_hidden @ X20 @ (k3_relat_1 @ X19))
% 0.20/0.62          | ~ (v1_relat_1 @ X19))),
% 0.20/0.62      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.62  thf('113', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r2_hidden @ X1 @ X0)
% 0.20/0.62          | ((X0) = (X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.62          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.62  thf('114', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('115', plain,
% 0.20/0.62      (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.20/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.62  thf('116', plain,
% 0.20/0.62      (![X0 : $i, X1 : $i]:
% 0.20/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.62          | ~ (v3_ordinal1 @ X0)
% 0.20/0.62          | (r2_hidden @ X1 @ X0)
% 0.20/0.62          | ((X0) = (X1))
% 0.20/0.62          | ~ (v3_ordinal1 @ X1)
% 0.20/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.62      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.20/0.62  thf('117', plain,
% 0.20/0.62      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.20/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | ((sk_B) = (sk_A))
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['107', '116'])).
% 0.20/0.62  thf('118', plain,
% 0.20/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('119', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('120', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('121', plain,
% 0.20/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.62        | ((sk_B) = (sk_A))
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.20/0.62  thf('122', plain, (((sk_A) != (sk_B))),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('123', plain,
% 0.20/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 0.20/0.62  thf('124', plain,
% 0.20/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.62        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.62      inference('sup-', [status(thm)], ['1', '123'])).
% 0.20/0.62  thf('125', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('126', plain,
% 0.20/0.62      (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['124', '125'])).
% 0.20/0.62  thf('127', plain,
% 0.20/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.62        | ((sk_B) = (sk_A))
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['0', '126'])).
% 0.20/0.62  thf('128', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('129', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('130', plain,
% 0.20/0.62      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.62        | ((sk_B) = (sk_A))
% 0.20/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.20/0.62  thf('131', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.62      inference('simplify', [status(thm)], ['130'])).
% 0.20/0.62  thf('132', plain, (((sk_A) != (sk_B))),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('133', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.62      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.20/0.62  thf('134', plain,
% 0.20/0.62      (![X26 : $i, X27 : $i]:
% 0.20/0.62         (~ (v3_ordinal1 @ X26)
% 0.20/0.62          | ((X27) = (k1_wellord1 @ (k1_wellord2 @ X26) @ X27))
% 0.20/0.62          | ~ (r2_hidden @ X27 @ X26)
% 0.20/0.62          | ~ (v3_ordinal1 @ X27))),
% 0.20/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.62  thf('135', plain,
% 0.20/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.62        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['133', '134'])).
% 0.20/0.62  thf('136', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('137', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.62  thf('138', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.20/0.62  thf('139', plain,
% 0.20/0.62      (![X7 : $i, X8 : $i]:
% 0.20/0.62         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 0.20/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.62  thf('140', plain,
% 0.20/0.62      ((~ (r2_hidden @ sk_A @ sk_A) | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.62      inference('sup-', [status(thm)], ['138', '139'])).
% 0.20/0.62  thf('141', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.62      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.20/0.62  thf('142', plain,
% 0.20/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.20/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.62  thf('143', plain,
% 0.20/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X12 @ (k3_relat_1 @ (k2_wellord1 @ X13 @ X14)))
% 0.20/0.62          | (r2_hidden @ X12 @ (k3_relat_1 @ X13))
% 0.20/0.62          | ~ (v1_relat_1 @ X13))),
% 0.20/0.62      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.20/0.62  thf('144', plain,
% 0.20/0.62      (![X0 : $i]:
% 0.20/0.62         (~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.20/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.62          | (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_A))))),
% 0.20/0.62      inference('sup-', [status(thm)], ['142', '143'])).
% 0.20/0.62  thf('145', plain,
% 0.20/0.62      (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.20/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.62  thf('146', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('147', plain,
% 0.20/0.62      (![X21 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X21)) = (X21))),
% 0.20/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.62  thf('148', plain,
% 0.20/0.62      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ sk_A))),
% 0.20/0.62      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.20/0.62  thf('149', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.62      inference('sup-', [status(thm)], ['141', '148'])).
% 0.20/0.62  thf('150', plain, (![X25 : $i]: (v1_relat_1 @ (k1_wellord2 @ X25))),
% 0.20/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.62  thf('151', plain, ($false),
% 0.20/0.62      inference('demod', [status(thm)], ['140', '149', '150'])).
% 0.20/0.62  
% 0.20/0.62  % SZS output end Refutation
% 0.20/0.62  
% 0.20/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
