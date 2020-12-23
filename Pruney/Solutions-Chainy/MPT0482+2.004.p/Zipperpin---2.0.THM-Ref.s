%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eUSWWNNesw

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:58 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 283 expanded)
%              Number of leaves         :   20 (  89 expanded)
%              Depth                    :   30
%              Number of atoms          : 1309 (3532 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( X5 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t77_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
         => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_relat_1])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_2 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_2 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( sk_D_2 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( sk_D_2 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( sk_D_2 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('39',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( sk_D_2 @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['40','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( X5 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( X5 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) @ ( sk_D @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eUSWWNNesw
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.46/1.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.46/1.67  % Solved by: fo/fo7.sh
% 1.46/1.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.67  % done 1031 iterations in 1.214s
% 1.46/1.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.46/1.67  % SZS output start Refutation
% 1.46/1.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.46/1.67  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.46/1.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.46/1.67  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.46/1.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.46/1.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.46/1.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.46/1.67  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.46/1.67  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.67  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.46/1.67  thf(dt_k5_relat_1, axiom,
% 1.46/1.67    (![A:$i,B:$i]:
% 1.46/1.67     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.46/1.67       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.46/1.67  thf('0', plain,
% 1.46/1.67      (![X16 : $i, X17 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X16)
% 1.46/1.67          | ~ (v1_relat_1 @ X17)
% 1.46/1.67          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 1.46/1.67      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.46/1.67  thf('1', plain,
% 1.46/1.67      (![X16 : $i, X17 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X16)
% 1.46/1.67          | ~ (v1_relat_1 @ X17)
% 1.46/1.67          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 1.46/1.67      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.46/1.67  thf('2', plain,
% 1.46/1.67      (![X16 : $i, X17 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X16)
% 1.46/1.67          | ~ (v1_relat_1 @ X17)
% 1.46/1.67          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 1.46/1.67      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.46/1.67  thf(d2_relat_1, axiom,
% 1.46/1.67    (![A:$i]:
% 1.46/1.67     ( ( v1_relat_1 @ A ) =>
% 1.46/1.67       ( ![B:$i]:
% 1.46/1.67         ( ( v1_relat_1 @ B ) =>
% 1.46/1.67           ( ( ( A ) = ( B ) ) <=>
% 1.46/1.67             ( ![C:$i,D:$i]:
% 1.46/1.67               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 1.46/1.67                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 1.46/1.67  thf('3', plain,
% 1.46/1.67      (![X4 : $i, X5 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X4)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 1.46/1.67             X5)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 1.46/1.67             X4)
% 1.46/1.67          | ((X5) = (X4))
% 1.46/1.67          | ~ (v1_relat_1 @ X5))),
% 1.46/1.67      inference('cnf', [status(esa)], [d2_relat_1])).
% 1.46/1.67  thf(d4_relat_1, axiom,
% 1.46/1.67    (![A:$i,B:$i]:
% 1.46/1.67     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.46/1.67       ( ![C:$i]:
% 1.46/1.67         ( ( r2_hidden @ C @ B ) <=>
% 1.46/1.67           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.46/1.67  thf('4', plain,
% 1.46/1.67      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.46/1.67         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 1.46/1.67          | (r2_hidden @ X9 @ X12)
% 1.46/1.67          | ((X12) != (k1_relat_1 @ X11)))),
% 1.46/1.67      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.46/1.67  thf('5', plain,
% 1.46/1.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.46/1.67         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 1.46/1.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 1.46/1.67      inference('simplify', [status(thm)], ['4'])).
% 1.46/1.67  thf('6', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X0)
% 1.46/1.67          | ((X0) = (X1))
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ 
% 1.46/1.67             X1)
% 1.46/1.67          | ~ (v1_relat_1 @ X1)
% 1.46/1.67          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['3', '5'])).
% 1.46/1.67  thf('7', plain,
% 1.46/1.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.46/1.67         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 1.46/1.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 1.46/1.67      inference('simplify', [status(thm)], ['4'])).
% 1.46/1.67  thf('8', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k1_relat_1 @ X1))
% 1.46/1.67          | ~ (v1_relat_1 @ X0)
% 1.46/1.67          | ((X1) = (X0))
% 1.46/1.67          | ~ (v1_relat_1 @ X1)
% 1.46/1.67          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['6', '7'])).
% 1.46/1.67  thf(d3_tarski, axiom,
% 1.46/1.67    (![A:$i,B:$i]:
% 1.46/1.67     ( ( r1_tarski @ A @ B ) <=>
% 1.46/1.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.46/1.67  thf('9', plain,
% 1.46/1.67      (![X1 : $i, X3 : $i]:
% 1.46/1.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf(t77_relat_1, conjecture,
% 1.46/1.67    (![A:$i,B:$i]:
% 1.46/1.67     ( ( v1_relat_1 @ B ) =>
% 1.46/1.67       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.46/1.67         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.46/1.67  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.67    (~( ![A:$i,B:$i]:
% 1.46/1.67        ( ( v1_relat_1 @ B ) =>
% 1.46/1.67          ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.46/1.67            ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ) )),
% 1.46/1.67    inference('cnf.neg', [status(esa)], [t77_relat_1])).
% 1.46/1.67  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('11', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         (~ (r2_hidden @ X0 @ X1)
% 1.46/1.67          | (r2_hidden @ X0 @ X2)
% 1.46/1.67          | ~ (r1_tarski @ X1 @ X2))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf('12', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['10', '11'])).
% 1.46/1.67  thf('13', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.46/1.67          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 1.46/1.67      inference('sup-', [status(thm)], ['9', '12'])).
% 1.46/1.67  thf('14', plain,
% 1.46/1.67      (![X1 : $i, X3 : $i]:
% 1.46/1.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf('15', plain,
% 1.46/1.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.46/1.67         (~ (r2_hidden @ X13 @ X12)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_2 @ X13 @ X11)) @ X11)
% 1.46/1.67          | ((X12) != (k1_relat_1 @ X11)))),
% 1.46/1.67      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.46/1.67  thf('16', plain,
% 1.46/1.67      (![X11 : $i, X13 : $i]:
% 1.46/1.67         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_2 @ X13 @ X11)) @ X11)
% 1.46/1.67          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 1.46/1.67      inference('simplify', [status(thm)], ['15'])).
% 1.46/1.67  thf('17', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.46/1.67              (sk_D_2 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 1.46/1.67             X0))),
% 1.46/1.67      inference('sup-', [status(thm)], ['14', '16'])).
% 1.46/1.67  thf(t74_relat_1, axiom,
% 1.46/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.67     ( ( v1_relat_1 @ D ) =>
% 1.46/1.67       ( ( r2_hidden @
% 1.46/1.67           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 1.46/1.67         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 1.46/1.67  thf('18', plain,
% 1.46/1.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.46/1.67         (~ (r2_hidden @ X19 @ X20)
% 1.46/1.67          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X20) @ X22))
% 1.46/1.67          | ~ (v1_relat_1 @ X22))),
% 1.46/1.67      inference('cnf', [status(esa)], [t74_relat_1])).
% 1.46/1.67  thf('19', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.46/1.67          | ~ (v1_relat_1 @ X0)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.46/1.67              (sk_D_2 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 1.46/1.67          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 1.46/1.67      inference('sup-', [status(thm)], ['17', '18'])).
% 1.46/1.67  thf('20', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.46/1.67              (sk_D_2 @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ sk_B)) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67          | ~ (v1_relat_1 @ sk_B)
% 1.46/1.67          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.46/1.67      inference('sup-', [status(thm)], ['13', '19'])).
% 1.46/1.67  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('22', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.46/1.67              (sk_D_2 @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ sk_B)) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.46/1.67      inference('demod', [status(thm)], ['20', '21'])).
% 1.46/1.67  thf('23', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r2_hidden @ 
% 1.46/1.67           (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.46/1.67            (sk_D_2 @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ sk_B)) @ 
% 1.46/1.67           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.46/1.67      inference('simplify', [status(thm)], ['22'])).
% 1.46/1.67  thf('24', plain,
% 1.46/1.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.46/1.67         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 1.46/1.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 1.46/1.67      inference('simplify', [status(thm)], ['4'])).
% 1.46/1.67  thf('25', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 1.46/1.67          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.46/1.67             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))))),
% 1.46/1.67      inference('sup-', [status(thm)], ['23', '24'])).
% 1.46/1.67  thf('26', plain,
% 1.46/1.67      (![X1 : $i, X3 : $i]:
% 1.46/1.67         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf('27', plain,
% 1.46/1.67      (((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 1.46/1.67         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 1.46/1.67        | (r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 1.46/1.67           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))))),
% 1.46/1.67      inference('sup-', [status(thm)], ['25', '26'])).
% 1.46/1.67  thf('28', plain,
% 1.46/1.67      ((r1_tarski @ (k1_relat_1 @ sk_B) @ 
% 1.46/1.67        (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('simplify', [status(thm)], ['27'])).
% 1.46/1.67  thf('29', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         (~ (r2_hidden @ X0 @ X1)
% 1.46/1.67          | (r2_hidden @ X0 @ X2)
% 1.46/1.67          | ~ (r1_tarski @ X1 @ X2))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf('30', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r2_hidden @ X0 @ 
% 1.46/1.67           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 1.46/1.67          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['28', '29'])).
% 1.46/1.67  thf('31', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X0)
% 1.46/1.67          | ((X0) = (sk_B))
% 1.46/1.67          | ~ (v1_relat_1 @ sk_B)
% 1.46/1.67          | (r2_hidden @ (sk_C_1 @ sk_B @ X0) @ (k1_relat_1 @ X0))
% 1.46/1.67          | (r2_hidden @ (sk_C_1 @ sk_B @ X0) @ 
% 1.46/1.67             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))))),
% 1.46/1.67      inference('sup-', [status(thm)], ['8', '30'])).
% 1.46/1.67  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('33', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X0)
% 1.46/1.67          | ((X0) = (sk_B))
% 1.46/1.67          | (r2_hidden @ (sk_C_1 @ sk_B @ X0) @ (k1_relat_1 @ X0))
% 1.46/1.67          | (r2_hidden @ (sk_C_1 @ sk_B @ X0) @ 
% 1.46/1.67             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))))),
% 1.46/1.67      inference('demod', [status(thm)], ['31', '32'])).
% 1.46/1.67  thf('34', plain,
% 1.46/1.67      (((r2_hidden @ 
% 1.46/1.67         (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 1.46/1.67        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 1.46/1.67        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('eq_fact', [status(thm)], ['33'])).
% 1.46/1.67  thf('35', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('36', plain,
% 1.46/1.67      (((r2_hidden @ 
% 1.46/1.67         (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 1.46/1.67        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.46/1.67  thf('37', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ sk_B)
% 1.46/1.67        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))))),
% 1.46/1.67      inference('sup-', [status(thm)], ['2', '36'])).
% 1.46/1.67  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.46/1.67  thf('39', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 1.46/1.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.46/1.67  thf('40', plain,
% 1.46/1.67      ((r2_hidden @ 
% 1.46/1.67        (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67        (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.46/1.67  thf('41', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.46/1.67              (sk_D_2 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 1.46/1.67             X0))),
% 1.46/1.67      inference('sup-', [status(thm)], ['14', '16'])).
% 1.46/1.67  thf('42', plain,
% 1.46/1.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.46/1.67         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X20) @ X22))
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 1.46/1.67          | ~ (v1_relat_1 @ X22))),
% 1.46/1.67      inference('cnf', [status(esa)], [t74_relat_1])).
% 1.46/1.67  thf('43', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.46/1.67           X2)
% 1.46/1.67          | ~ (v1_relat_1 @ X0)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ 
% 1.46/1.67              (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.46/1.67              (sk_D_2 @ 
% 1.46/1.67               (sk_C @ X2 @ 
% 1.46/1.67                (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.46/1.67               (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.46/1.67             X0))),
% 1.46/1.67      inference('sup-', [status(thm)], ['41', '42'])).
% 1.46/1.67  thf('44', plain,
% 1.46/1.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.46/1.67         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 1.46/1.67          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 1.46/1.67      inference('simplify', [status(thm)], ['4'])).
% 1.46/1.67  thf('45', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X0)
% 1.46/1.67          | (r1_tarski @ 
% 1.46/1.67             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X2)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.46/1.67             (k1_relat_1 @ X0)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['43', '44'])).
% 1.46/1.67  thf('46', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['10', '11'])).
% 1.46/1.67  thf('47', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         ((r1_tarski @ 
% 1.46/1.67           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)) @ X1)
% 1.46/1.67          | ~ (v1_relat_1 @ sk_B)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (sk_C @ X1 @ 
% 1.46/1.67              (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))) @ 
% 1.46/1.67             sk_A))),
% 1.46/1.67      inference('sup-', [status(thm)], ['45', '46'])).
% 1.46/1.67  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('49', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         ((r1_tarski @ 
% 1.46/1.67           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)) @ X1)
% 1.46/1.67          | (r2_hidden @ 
% 1.46/1.67             (sk_C @ X1 @ 
% 1.46/1.67              (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))) @ 
% 1.46/1.67             sk_A))),
% 1.46/1.67      inference('demod', [status(thm)], ['47', '48'])).
% 1.46/1.67  thf('50', plain,
% 1.46/1.67      (![X1 : $i, X3 : $i]:
% 1.46/1.67         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf('51', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         ((r1_tarski @ 
% 1.46/1.67           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)) @ sk_A)
% 1.46/1.67          | (r1_tarski @ 
% 1.46/1.67             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)) @ sk_A))),
% 1.46/1.67      inference('sup-', [status(thm)], ['49', '50'])).
% 1.46/1.67  thf('52', plain,
% 1.46/1.67      (![X0 : $i]:
% 1.46/1.67         (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)) @ 
% 1.46/1.67          sk_A)),
% 1.46/1.67      inference('simplify', [status(thm)], ['51'])).
% 1.46/1.67  thf('53', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         (~ (r2_hidden @ X0 @ X1)
% 1.46/1.67          | (r2_hidden @ X0 @ X2)
% 1.46/1.67          | ~ (r1_tarski @ X1 @ X2))),
% 1.46/1.67      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.67  thf('54', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i]:
% 1.46/1.67         ((r2_hidden @ X1 @ sk_A)
% 1.46/1.67          | ~ (r2_hidden @ X1 @ 
% 1.46/1.67               (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))))),
% 1.46/1.67      inference('sup-', [status(thm)], ['52', '53'])).
% 1.46/1.67  thf('55', plain,
% 1.46/1.67      ((r2_hidden @ 
% 1.46/1.67        (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ sk_A)),
% 1.46/1.67      inference('sup-', [status(thm)], ['40', '54'])).
% 1.46/1.67  thf('56', plain,
% 1.46/1.67      (![X4 : $i, X5 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X4)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 1.46/1.67             X5)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 1.46/1.67             X4)
% 1.46/1.67          | ((X5) = (X4))
% 1.46/1.67          | ~ (v1_relat_1 @ X5))),
% 1.46/1.67      inference('cnf', [status(esa)], [d2_relat_1])).
% 1.46/1.67  thf('57', plain,
% 1.46/1.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.46/1.67         (~ (r2_hidden @ X19 @ X20)
% 1.46/1.67          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X20) @ X22))
% 1.46/1.67          | ~ (v1_relat_1 @ X22))),
% 1.46/1.67      inference('cnf', [status(esa)], [t74_relat_1])).
% 1.46/1.67  thf('58', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X1)
% 1.46/1.67          | ((X1) = (X0))
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 1.46/1.67             X1)
% 1.46/1.67          | ~ (v1_relat_1 @ X0)
% 1.46/1.67          | ~ (v1_relat_1 @ X0)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 1.46/1.67          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.46/1.67      inference('sup-', [status(thm)], ['56', '57'])).
% 1.46/1.67  thf('59', plain,
% 1.46/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.67         (~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 1.46/1.67          | ~ (v1_relat_1 @ X0)
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 1.46/1.67             X1)
% 1.46/1.67          | ((X1) = (X0))
% 1.46/1.67          | ~ (v1_relat_1 @ X1))),
% 1.46/1.67      inference('simplify', [status(thm)], ['58'])).
% 1.46/1.67  thf('60', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (k4_tarski @ 
% 1.46/1.67            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ~ (v1_relat_1 @ sk_B)
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (k4_tarski @ 
% 1.46/1.67            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['55', '59'])).
% 1.46/1.67  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('62', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (k4_tarski @ 
% 1.46/1.67            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (k4_tarski @ 
% 1.46/1.67            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('demod', [status(thm)], ['60', '61'])).
% 1.46/1.67  thf('63', plain,
% 1.46/1.67      (((r2_hidden @ 
% 1.46/1.67         (k4_tarski @ 
% 1.46/1.67          (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67          (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67         (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 1.46/1.67        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('simplify', [status(thm)], ['62'])).
% 1.46/1.67  thf('64', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('65', plain,
% 1.46/1.67      (((r2_hidden @ 
% 1.46/1.67         (k4_tarski @ 
% 1.46/1.67          (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67          (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67         (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 1.46/1.67  thf('66', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ sk_B)
% 1.46/1.67        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (k4_tarski @ 
% 1.46/1.67            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['1', '65'])).
% 1.46/1.67  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('68', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 1.46/1.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.46/1.67  thf('69', plain,
% 1.46/1.67      ((r2_hidden @ 
% 1.46/1.67        (k4_tarski @ 
% 1.46/1.67         (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67         (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 1.46/1.67      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.46/1.67  thf('70', plain,
% 1.46/1.67      (![X4 : $i, X5 : $i]:
% 1.46/1.67         (~ (v1_relat_1 @ X4)
% 1.46/1.67          | ~ (r2_hidden @ 
% 1.46/1.67               (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X5)
% 1.46/1.67          | ~ (r2_hidden @ 
% 1.46/1.67               (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X4)
% 1.46/1.67          | ((X5) = (X4))
% 1.46/1.67          | ~ (v1_relat_1 @ X5))),
% 1.46/1.67      inference('cnf', [status(esa)], [d2_relat_1])).
% 1.46/1.67  thf('71', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 1.46/1.67        | ~ (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ 
% 1.46/1.67              (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67              (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67             sk_B)
% 1.46/1.67        | ~ (v1_relat_1 @ sk_B))),
% 1.46/1.67      inference('sup-', [status(thm)], ['69', '70'])).
% 1.46/1.67  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('73', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))
% 1.46/1.67        | ~ (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ 
% 1.46/1.67              (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67              (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67             sk_B))),
% 1.46/1.67      inference('demod', [status(thm)], ['71', '72'])).
% 1.46/1.67  thf('74', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('75', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 1.46/1.67        | ~ (r2_hidden @ 
% 1.46/1.67             (k4_tarski @ 
% 1.46/1.67              (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67              (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67             sk_B))),
% 1.46/1.67      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 1.46/1.67  thf('76', plain,
% 1.46/1.67      ((r2_hidden @ 
% 1.46/1.67        (k4_tarski @ 
% 1.46/1.67         (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67         (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 1.46/1.67      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.46/1.67  thf('77', plain,
% 1.46/1.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.46/1.67         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ 
% 1.46/1.67             (k5_relat_1 @ (k6_relat_1 @ X20) @ X22))
% 1.46/1.67          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ X22)
% 1.46/1.67          | ~ (v1_relat_1 @ X22))),
% 1.46/1.67      inference('cnf', [status(esa)], [t74_relat_1])).
% 1.46/1.67  thf('78', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ sk_B)
% 1.46/1.67        | (r2_hidden @ 
% 1.46/1.67           (k4_tarski @ 
% 1.46/1.67            (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67            (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67           sk_B))),
% 1.46/1.67      inference('sup-', [status(thm)], ['76', '77'])).
% 1.46/1.67  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('80', plain,
% 1.46/1.67      ((r2_hidden @ 
% 1.46/1.67        (k4_tarski @ 
% 1.46/1.67         (sk_C_1 @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) @ 
% 1.46/1.67         (sk_D @ sk_B @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))) @ 
% 1.46/1.67        sk_B)),
% 1.46/1.67      inference('demod', [status(thm)], ['78', '79'])).
% 1.46/1.67  thf('81', plain,
% 1.46/1.67      (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 1.46/1.67      inference('demod', [status(thm)], ['75', '80'])).
% 1.46/1.67  thf('82', plain,
% 1.46/1.67      ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.46/1.67      inference('sup-', [status(thm)], ['0', '81'])).
% 1.46/1.67  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.67  thf('84', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 1.46/1.67      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.46/1.67  thf('85', plain, ($false),
% 1.46/1.67      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.46/1.67  
% 1.46/1.67  % SZS output end Refutation
% 1.46/1.67  
% 1.46/1.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
