%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xIXgaDxYcI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:26 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 180 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :   30
%              Number of atoms          :  909 (1809 expanded)
%              Number of equality atoms :   10 (  64 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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
    ! [X9: $i,X10: $i] :
      ( ( X10
       != ( k1_wellord2 @ X9 ) )
      | ( ( k3_relat_1 @ X10 )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('1',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X9 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
        = X9 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
      = X9 ) ),
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
    ! [X6: $i] :
      ( ( r2_hidden @ ( sk_B @ X6 ) @ ( k3_relat_1 @ X6 ) )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( sk_C @ X6 ) @ ( k3_relat_1 @ X6 ) )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( sk_B @ X6 ) @ ( k3_relat_1 @ X6 ) )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v3_ordinal1 @ ( k3_relat_1 @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('27',plain,(
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

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('32',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X9 ) )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('34',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ X6 ) @ ( sk_C @ X6 ) ) @ X6 )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_C @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) ) @ ( sk_B @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 ) @ ( sk_B @ X6 ) ) @ X6 )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t4_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_wellord2])).

thf('65',plain,(
    ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xIXgaDxYcI
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 112 iterations in 0.087s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.55  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.37/0.55  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.37/0.55  thf(d1_wellord2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ B ) =>
% 0.37/0.55       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.37/0.55         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.37/0.55           ( ![C:$i,D:$i]:
% 0.37/0.55             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.37/0.55               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.37/0.55                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]:
% 0.37/0.55         (((X10) != (k1_wellord2 @ X9))
% 0.37/0.55          | ((k3_relat_1 @ X10) = (X9))
% 0.37/0.55          | ~ (v1_relat_1 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X9 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X9))
% 0.37/0.55          | ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.55  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.37/0.55  thf('2', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('3', plain, (![X9 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9))),
% 0.37/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(l4_wellord1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( v6_relat_2 @ A ) <=>
% 0.37/0.55         ( ![B:$i,C:$i]:
% 0.37/0.55           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.37/0.55                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.37/0.55                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.37/0.55                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_B @ X6) @ (k3_relat_1 @ X6))
% 0.37/0.55          | (v6_relat_2 @ X6)
% 0.37/0.55          | ~ (v1_relat_1 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain, (![X9 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9))),
% 0.37/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ X6) @ (k3_relat_1 @ X6))
% 0.37/0.55          | (v6_relat_2 @ X6)
% 0.37/0.55          | ~ (v1_relat_1 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf(t23_ordinal1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i]:
% 0.37/0.55         ((v3_ordinal1 @ X4) | ~ (v3_ordinal1 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain, (![X9 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9))),
% 0.37/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_B @ X6) @ (k3_relat_1 @ X6))
% 0.37/0.55          | (v6_relat_2 @ X6)
% 0.37/0.55          | ~ (v1_relat_1 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i]:
% 0.37/0.55         ((v3_ordinal1 @ X4) | ~ (v3_ordinal1 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ (k3_relat_1 @ X0))
% 0.37/0.55          | (v3_ordinal1 @ (sk_B @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v3_ordinal1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.55  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v3_ordinal1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v3_ordinal1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(connectedness_r1_ordinal1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.55       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.55          | (r1_ordinal1 @ X1 @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.37/0.55  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.55       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X2)
% 0.37/0.55          | ~ (v3_ordinal1 @ X3)
% 0.37/0.55          | (r1_tarski @ X2 @ X3)
% 0.37/0.55          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_ordinal1 @ X0 @ X1)
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | (r1_tarski @ X1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ X1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (r1_ordinal1 @ X0 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (((X10) != (k1_wellord2 @ X9))
% 0.37/0.55          | ~ (r2_hidden @ X11 @ X9)
% 0.37/0.55          | ~ (r2_hidden @ X12 @ X9)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.37/0.55          | ~ (r1_tarski @ X11 @ X12)
% 0.37/0.55          | ~ (v1_relat_1 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ (k1_wellord2 @ X9))
% 0.37/0.55          | ~ (r1_tarski @ X11 @ X12)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.37/0.55          | ~ (r2_hidden @ X12 @ X9)
% 0.37/0.55          | ~ (r2_hidden @ X11 @ X9))),
% 0.37/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.55  thf('33', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X11 @ X12)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.37/0.55          | ~ (r2_hidden @ X12 @ X9)
% 0.37/0.55          | ~ (r2_hidden @ X11 @ X9))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r1_ordinal1 @ X0 @ X1)
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | ~ (r2_hidden @ X1 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X0 @ X2)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ X2)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['30', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.37/0.55             (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ X1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | (r1_ordinal1 @ X1 @ (sk_B @ (k1_wellord2 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (r1_ordinal1 @ X1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | ~ (r2_hidden @ X1 @ X0)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.37/0.55             (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r2_hidden @ (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ X1) @ 
% 0.37/0.55           (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ X1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ X1)
% 0.37/0.55          | (r1_ordinal1 @ X1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ 
% 0.37/0.55           (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55            (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55           (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ 
% 0.37/0.55           (k4_tarski @ (sk_B @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55            (sk_C @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55           (k1_wellord2 @ X0))
% 0.37/0.55          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ (k4_tarski @ (sk_B @ X6) @ (sk_C @ X6)) @ X6)
% 0.37/0.55          | (v6_relat_2 @ X6)
% 0.37/0.55          | ~ (v1_relat_1 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.55  thf('45', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55           (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X2)
% 0.37/0.55          | ~ (v3_ordinal1 @ X3)
% 0.37/0.55          | (r1_tarski @ X2 @ X3)
% 0.37/0.55          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '49'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55           (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ (sk_C @ (k1_wellord2 @ X0)))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55             (sk_B @ (k1_wellord2 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55           (sk_B @ (k1_wellord2 @ X0)))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X11 @ X12)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.37/0.55          | ~ (r2_hidden @ X12 @ X9)
% 0.37/0.55          | ~ (r2_hidden @ X11 @ X9))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ (sk_C @ (k1_wellord2 @ X0)) @ X1)
% 0.37/0.55          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X1)
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '55'])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (sk_B @ (k1_wellord2 @ X0)) @ X0)
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '57'])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0)) @ 
% 0.37/0.55              (sk_B @ (k1_wellord2 @ X0))) @ 
% 0.37/0.55             (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6) @ (sk_B @ X6)) @ X6)
% 0.37/0.55          | (v6_relat_2 @ X6)
% 0.37/0.55          | ~ (v1_relat_1 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf('62', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v6_relat_2 @ (k1_wellord2 @ X0))
% 0.37/0.55          | ~ (v3_ordinal1 @ X0)
% 0.37/0.55          | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v6_relat_2 @ (k1_wellord2 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.55  thf(t4_wellord2, conjecture,
% 0.37/0.55    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( v3_ordinal1 @ A ) => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t4_wellord2])).
% 0.37/0.55  thf('65', plain, (~ (v6_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('66', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.37/0.55  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('68', plain, ($false), inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
