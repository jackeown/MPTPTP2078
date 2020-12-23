%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0939+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0GTty0Afzz

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 142 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   33
%              Number of atoms          : 1132 (1595 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r6_relat_2_type,type,(
    r6_relat_2: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(d6_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r6_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( C != D )
                & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ~ ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X9 @ X10 ) @ X9 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X9 @ X10 ) @ X9 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r6_relat_2 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc5_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v3_ordinal1 @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc5_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r6_relat_2 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_D_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r6_relat_2 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc5_ordinal1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r6_relat_2 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r6_relat_2 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_D_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X9 @ X10 ) @ X9 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r6_relat_2 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_ordinal1 @ X2 @ X3 )
      | ( r1_ordinal1 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X6 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('21',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r6_relat_2 @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r6_relat_2 @ X0 @ X1 )
      | ( r1_ordinal1 @ X2 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) @ ( k1_wellord2 @ X1 ) )
      | ( r6_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( r6_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r6_relat_2 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r6_relat_2 @ X2 @ X0 )
      | ( r1_ordinal1 @ ( sk_D_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 @ X2 ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X2 ) @ ( sk_D_1 @ X0 @ X1 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r6_relat_2 @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X2 ) @ ( sk_D_1 @ X1 @ X0 ) ) @ ( k1_wellord2 @ X1 ) )
      | ( r1_ordinal1 @ ( sk_D_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X2 ) )
      | ( r6_relat_2 @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r6_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r6_relat_2 @ X2 @ X1 )
      | ( r1_ordinal1 @ ( sk_D_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X2 ) @ ( sk_D_1 @ X1 @ X0 ) ) @ ( k1_wellord2 @ X1 ) )
      | ( r6_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X9 @ X10 ) @ ( sk_D_1 @ X9 @ X10 ) ) @ X10 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('34',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('35',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','39'])).

thf('41',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','43'])).

thf('45',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_wellord2 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X7 @ X5 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X9 @ X10 ) @ ( sk_C_1 @ X9 @ X10 ) ) @ X10 )
      | ( r6_relat_2 @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
       != ( k1_wellord2 @ X5 ) )
      | ( ( k3_relat_1 @ X6 )
        = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('64',plain,(
    ! [X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X5 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X5 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('66',plain,(
    ! [X5: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(d14_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ( r6_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X4: $i] :
      ( ~ ( r6_relat_2 @ X4 @ ( k3_relat_1 @ X4 ) )
      | ( v6_relat_2 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r6_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf(t4_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_wellord2])).

thf('72',plain,(
    ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['73','74'])).


%------------------------------------------------------------------------------
