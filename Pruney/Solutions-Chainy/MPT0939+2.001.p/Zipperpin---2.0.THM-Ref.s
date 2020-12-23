%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hOnfVwMxth

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:26 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 209 expanded)
%              Number of leaves         :   23 (  71 expanded)
%              Depth                    :   34
%              Number of atoms          : 1103 (2117 expanded)
%              Number of equality atoms :   11 (  71 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
       != ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('1',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
        = X13 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X10 ) @ ( k3_relat_1 @ X10 ) )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( r2_hidden @ ( sk_C @ X10 ) @ ( k3_relat_1 @ X10 ) )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( r2_hidden @ ( sk_C @ X10 ) @ ( k3_relat_1 @ X10 ) )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v3_ordinal1 @ ( k3_relat_1 @ X0 ) )
      | ( v3_ordinal1 @ ( sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X10 ) @ ( k3_relat_1 @ X10 ) )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v3_ordinal1 @ ( k3_relat_1 @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X9 @ X8 )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( v3_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_ordinal1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14
       != ( k1_wellord2 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X14 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('44',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X13 ) )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ ( k1_wellord2 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X15 @ X13 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ ( k1_wellord2 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X15 @ X13 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_ordinal1 @ X1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_ordinal1 @ X1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_ordinal1 @ X1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X10 ) @ ( sk_C @ X10 ) ) @ X10 )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_ordinal1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ ( k1_wellord2 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X15 @ X13 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B_1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X10 ) @ ( sk_B_1 @ X10 ) ) @ X10 )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(t4_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_wellord2])).

thf('79',plain,(
    ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hOnfVwMxth
% 0.15/0.37  % Computer   : n017.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:46:17 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 369 iterations in 0.355s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.58/0.81  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.81  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.58/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.81  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.58/0.81  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.58/0.81  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.58/0.81  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.58/0.81  thf(sk_C_type, type, sk_C: $i > $i).
% 0.58/0.81  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(d1_wellord2, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ B ) =>
% 0.58/0.81       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.58/0.81         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.58/0.81           ( ![C:$i,D:$i]:
% 0.58/0.81             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.58/0.81               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.58/0.81                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.58/0.81  thf('0', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i]:
% 0.58/0.81         (((X14) != (k1_wellord2 @ X13))
% 0.58/0.81          | ((k3_relat_1 @ X14) = (X13))
% 0.58/0.81          | ~ (v1_relat_1 @ X14))),
% 0.58/0.81      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.58/0.81  thf('1', plain,
% 0.58/0.81      (![X13 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ (k1_wellord2 @ X13))
% 0.58/0.81          | ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.58/0.81  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.58/0.81  thf('2', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.81  thf('3', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.58/0.81      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf(l4_wellord1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( ( v6_relat_2 @ A ) <=>
% 0.58/0.81         ( ![B:$i,C:$i]:
% 0.58/0.81           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.58/0.81                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.58/0.81                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.58/0.81                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      (![X10 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_B_1 @ X10) @ (k3_relat_1 @ X10))
% 0.58/0.81          | (v6_relat_2 @ X10)
% 0.58/0.81          | ~ (v1_relat_1 @ X10))),
% 0.58/0.81      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.81  thf('6', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.81  thf('7', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.81  thf('8', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.58/0.81      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf('9', plain,
% 0.58/0.81      (![X10 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_C @ X10) @ (k3_relat_1 @ X10))
% 0.58/0.81          | (v6_relat_2 @ X10)
% 0.58/0.81          | ~ (v1_relat_1 @ X10))),
% 0.58/0.81      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.58/0.81  thf('10', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.81          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.81  thf('11', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.81  thf('13', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.58/0.81      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (![X10 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_C @ X10) @ (k3_relat_1 @ X10))
% 0.58/0.81          | (v6_relat_2 @ X10)
% 0.58/0.81          | ~ (v1_relat_1 @ X10))),
% 0.58/0.81      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.58/0.81  thf(t23_ordinal1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.58/0.81  thf('15', plain,
% 0.58/0.81      (![X6 : $i, X7 : $i]:
% 0.58/0.81         ((v3_ordinal1 @ X6) | ~ (v3_ordinal1 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v6_relat_2 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ (k3_relat_1 @ X0))
% 0.58/0.81          | (v3_ordinal1 @ (sk_C @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['13', '16'])).
% 0.58/0.81  thf('18', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.81  thf('20', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.58/0.81      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf('21', plain,
% 0.58/0.81      (![X10 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_B_1 @ X10) @ (k3_relat_1 @ X10))
% 0.58/0.81          | (v6_relat_2 @ X10)
% 0.58/0.81          | ~ (v1_relat_1 @ X10))),
% 0.58/0.81      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.58/0.81  thf('22', plain,
% 0.58/0.81      (![X6 : $i, X7 : $i]:
% 0.58/0.81         ((v3_ordinal1 @ X6) | ~ (v3_ordinal1 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v1_relat_1 @ X0)
% 0.58/0.81          | (v6_relat_2 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ (k3_relat_1 @ X0))
% 0.58/0.81          | (v3_ordinal1 @ (sk_B_1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.81  thf('24', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['20', '23'])).
% 0.58/0.81  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.81  thf('26', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.81  thf('27', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.81  thf('28', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['10', '11'])).
% 0.58/0.81  thf('29', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.81  thf(cc1_ordinal1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.58/0.81  thf('30', plain, (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v1_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (v3_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.81          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['5', '6'])).
% 0.58/0.81  thf(t26_ordinal1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v3_ordinal1 @ A ) =>
% 0.58/0.81       ( ![B:$i]:
% 0.58/0.81         ( ( v3_ordinal1 @ B ) =>
% 0.58/0.81           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.81  thf('34', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X8)
% 0.58/0.81          | (r1_ordinal1 @ X9 @ X8)
% 0.58/0.81          | (r2_hidden @ X8 @ X9)
% 0.58/0.81          | ~ (v3_ordinal1 @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.58/0.81  thf(d2_ordinal1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_ordinal1 @ A ) <=>
% 0.58/0.81       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.58/0.81  thf('35', plain,
% 0.58/0.81      (![X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X1 @ X2)
% 0.58/0.81          | (r1_tarski @ X1 @ X2)
% 0.58/0.81          | ~ (v1_ordinal1 @ X2))),
% 0.58/0.81      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.58/0.81  thf('36', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1)
% 0.58/0.81          | ~ (v1_ordinal1 @ X0)
% 0.58/0.81          | (r1_tarski @ X1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.81  thf(redefinition_r1_ordinal1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.58/0.81       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.58/0.81  thf('37', plain,
% 0.58/0.81      (![X4 : $i, X5 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X4)
% 0.58/0.81          | ~ (v3_ordinal1 @ X5)
% 0.58/0.81          | (r1_ordinal1 @ X4 @ X5)
% 0.58/0.81          | ~ (r1_tarski @ X4 @ X5))),
% 0.58/0.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.58/0.81  thf('38', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (v1_ordinal1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1)
% 0.58/0.81          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (r1_ordinal1 @ X1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r1_ordinal1 @ X1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1)
% 0.58/0.81          | ~ (v1_ordinal1 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['38'])).
% 0.58/0.81  thf('40', plain,
% 0.58/0.81      (![X4 : $i, X5 : $i]:
% 0.58/0.81         (~ (v3_ordinal1 @ X4)
% 0.58/0.81          | ~ (v3_ordinal1 @ X5)
% 0.58/0.81          | (r1_tarski @ X4 @ X5)
% 0.58/0.81          | ~ (r1_ordinal1 @ X4 @ X5))),
% 0.58/0.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (v1_ordinal1 @ X1)
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1)
% 0.58/0.81          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.81          | (r1_tarski @ X1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r1_tarski @ X1 @ X0)
% 0.58/0.81          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.81          | ~ (v3_ordinal1 @ X1)
% 0.58/0.81          | ~ (v3_ordinal1 @ X0)
% 0.58/0.81          | ~ (v1_ordinal1 @ X1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.82         (((X14) != (k1_wellord2 @ X13))
% 0.58/0.82          | ~ (r2_hidden @ X15 @ X13)
% 0.58/0.82          | ~ (r2_hidden @ X16 @ X13)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ X15 @ X16) @ X14)
% 0.58/0.82          | ~ (r1_tarski @ X15 @ X16)
% 0.58/0.82          | ~ (v1_relat_1 @ X14))),
% 0.58/0.82      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ (k1_wellord2 @ X13))
% 0.58/0.82          | ~ (r1_tarski @ X15 @ X16)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ X15 @ X16) @ (k1_wellord2 @ X13))
% 0.58/0.82          | ~ (r2_hidden @ X16 @ X13)
% 0.58/0.82          | ~ (r2_hidden @ X15 @ X13))),
% 0.58/0.82      inference('simplify', [status(thm)], ['43'])).
% 0.58/0.82  thf('45', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.82  thf('46', plain,
% 0.58/0.82      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.58/0.82         (~ (r1_tarski @ X15 @ X16)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ X15 @ X16) @ (k1_wellord2 @ X13))
% 0.58/0.82          | ~ (r2_hidden @ X16 @ X13)
% 0.58/0.82          | ~ (r2_hidden @ X15 @ X13))),
% 0.58/0.82      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.82  thf('47', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         (~ (v1_ordinal1 @ X1)
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (v3_ordinal1 @ X1)
% 0.58/0.82          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.82          | ~ (r2_hidden @ X1 @ X2)
% 0.58/0.82          | ~ (r2_hidden @ X0 @ X2)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ X2)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['42', '46'])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.58/0.82             (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (r2_hidden @ X1 @ X0)
% 0.58/0.82          | (r1_ordinal1 @ X1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X1)
% 0.58/0.82          | ~ (v1_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['33', '47'])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (v1_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X1)
% 0.58/0.82          | (r1_ordinal1 @ X1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (r2_hidden @ X1 @ X0)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.58/0.82             (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['32', '48'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.58/0.82           (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (r2_hidden @ X1 @ X0)
% 0.58/0.82          | (r1_ordinal1 @ X1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X1)
% 0.58/0.82          | ~ (v1_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['49'])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (v3_ordinal1 @ X1)
% 0.58/0.82          | (r1_ordinal1 @ X1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (r2_hidden @ X1 @ X0)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.58/0.82             (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['31', '50'])).
% 0.58/0.82  thf('52', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.58/0.82           (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (r2_hidden @ X1 @ X0)
% 0.58/0.82          | (r1_ordinal1 @ X1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X1)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['51'])).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.82          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['28', '52'])).
% 0.58/0.82  thf('54', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r2_hidden @ 
% 0.58/0.82           (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82            (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82           (k1_wellord2 @ X0))
% 0.58/0.82          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['53'])).
% 0.58/0.82  thf('55', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['27', '54'])).
% 0.58/0.82  thf('56', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r2_hidden @ 
% 0.58/0.82           (k4_tarski @ (sk_B_1 @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82            (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82           (k1_wellord2 @ X0))
% 0.58/0.82          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.82  thf('57', plain,
% 0.58/0.82      (![X10 : $i]:
% 0.58/0.82         (~ (r2_hidden @ (k4_tarski @ (sk_B_1 @ X10) @ (sk_C @ X10)) @ X10)
% 0.58/0.82          | (v6_relat_2 @ X10)
% 0.58/0.82          | ~ (v1_relat_1 @ X10))),
% 0.58/0.82      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.58/0.82  thf('58', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.82  thf('59', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.82  thf('60', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['58', '59'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82           (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['60'])).
% 0.58/0.82  thf('62', plain,
% 0.58/0.82      (![X4 : $i, X5 : $i]:
% 0.58/0.82         (~ (v3_ordinal1 @ X4)
% 0.58/0.82          | ~ (v3_ordinal1 @ X5)
% 0.58/0.82          | (r1_tarski @ X4 @ X5)
% 0.58/0.82          | ~ (r1_ordinal1 @ X4 @ X5))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.58/0.82  thf('63', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['61', '62'])).
% 0.58/0.82  thf('64', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.82          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['26', '63'])).
% 0.58/0.82  thf('65', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82           (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.82  thf('66', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82             (sk_B_1 @ (k1_wellord2 @ X0))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['19', '65'])).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82           (sk_B_1 @ (k1_wellord2 @ X0)))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['66'])).
% 0.58/0.82  thf('68', plain,
% 0.58/0.82      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.58/0.82         (~ (r1_tarski @ X15 @ X16)
% 0.58/0.82          | (r2_hidden @ (k4_tarski @ X15 @ X16) @ (k1_wellord2 @ X13))
% 0.58/0.82          | ~ (r2_hidden @ X16 @ X13)
% 0.58/0.82          | ~ (r2_hidden @ X15 @ X13))),
% 0.58/0.82      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.82  thf('69', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X1)
% 0.58/0.82          | ~ (r2_hidden @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X1)
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_B_1 @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X1)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['67', '68'])).
% 0.58/0.82  thf('70', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_B_1 @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (r2_hidden @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['12', '69'])).
% 0.58/0.82  thf('71', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (r2_hidden @ (sk_B_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_B_1 @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['70'])).
% 0.58/0.82  thf('72', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_B_1 @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['7', '71'])).
% 0.58/0.82  thf('73', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (r2_hidden @ 
% 0.58/0.82             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.58/0.82              (sk_B_1 @ (k1_wellord2 @ X0))) @ 
% 0.58/0.82             (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['72'])).
% 0.58/0.82  thf('74', plain,
% 0.58/0.82      (![X10 : $i]:
% 0.58/0.82         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X10) @ (sk_B_1 @ X10)) @ X10)
% 0.58/0.82          | (v6_relat_2 @ X10)
% 0.58/0.82          | ~ (v1_relat_1 @ X10))),
% 0.58/0.82      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.58/0.82  thf('75', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.82  thf('76', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.58/0.82  thf('77', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.58/0.82          | ~ (v3_ordinal1 @ X0)
% 0.58/0.82          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['75', '76'])).
% 0.58/0.82  thf('78', plain,
% 0.58/0.82      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['77'])).
% 0.58/0.82  thf(t4_wellord2, conjecture,
% 0.58/0.82    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i]:
% 0.58/0.82        ( ( v3_ordinal1 @ A ) => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t4_wellord2])).
% 0.58/0.82  thf('79', plain, (~ (v6_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('80', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.58/0.82      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.82  thf('81', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('82', plain, ($false), inference('demod', [status(thm)], ['80', '81'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
