%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0745+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EurWU3QQIT

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:25 EST 2020

% Result     : Theorem 19.73s
% Output     : Refutation 19.73s
% Verified   : 
% Statistics : Number of formulae       :  192 (1628 expanded)
%              Number of leaves         :   21 ( 464 expanded)
%              Depth                    :   32
%              Number of atoms          : 1792 (16484 expanded)
%              Number of equality atoms :   23 ( 458 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
    <=> ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ X13 )
      | ~ ( v2_ordinal1 @ X13 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_ordinal1])).

thf(t35_ordinal1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( v3_ordinal1 @ B ) )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v3_ordinal1 @ B ) )
       => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_ordinal1])).

thf('1',plain,(
    ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ X15 )
      | ( X17
       != ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('5',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B_1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X25: $i] :
      ( ( v3_ordinal1 @ X25 )
      | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('10',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ X18 @ ( sk_D_1 @ X18 @ X15 ) )
      | ( X17
       != ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ ( sk_D_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B_1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_B_1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B_1 @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( v3_ordinal1 @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('18',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X25: $i] :
      ( ( v3_ordinal1 @ X25 )
      | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('23',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ ( sk_D_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_C @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_C @ ( k3_tarski @ sk_A ) ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( v3_ordinal1 @ ( sk_C @ ( k3_tarski @ sk_A ) ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( r2_hidden @ X24 @ X23 )
      | ( X24 = X23 )
      | ( r2_hidden @ X23 @ X24 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 ) @ ( sk_B_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( sk_C @ X0 ) )
      | ( ( sk_C @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X0 ) )
      | ( v2_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( ( sk_C @ ( k3_tarski @ sk_A ) )
      = ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( r2_hidden @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) @ ( sk_C @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) @ ( sk_C @ ( k3_tarski @ sk_A ) ) )
    | ( ( sk_C @ ( k3_tarski @ sk_A ) )
      = ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( ( sk_C @ ( k3_tarski @ sk_A ) )
      = ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( r2_hidden @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) @ ( sk_C @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_B_1 @ ( k3_tarski @ sk_A ) ) @ ( sk_C @ ( k3_tarski @ sk_A ) ) )
    | ( ( sk_C @ ( k3_tarski @ sk_A ) )
      = ( sk_B_1 @ ( k3_tarski @ sk_A ) ) )
    | ( v2_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X7 ) @ ( sk_C @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('37',plain,
    ( ( v2_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( ( sk_C @ ( k3_tarski @ sk_A ) )
      = ( sk_B_1 @ ( k3_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i] :
      ( ( v2_ordinal1 @ X7 )
      | ( ( sk_B_1 @ X7 )
       != ( sk_C @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('39',plain,(
    v2_ordinal1 @ ( k3_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','39'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('43',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( v3_ordinal1 @ X25 )
      | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('48',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v2_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ X13 )
      | ~ ( v2_ordinal1 @ X13 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_ordinal1])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('51',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ ( sk_D_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ~ ( v2_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) )
    | ~ ( v1_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( v1_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) )
    | ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) )
    | ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) )
    | ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['57','61'])).

thf('63',plain,(
    ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','39'])).

thf('64',plain,(
    v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('66',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v3_ordinal1 @ X21 )
      | ~ ( v3_ordinal1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( r2_hidden @ X24 @ X23 )
      | ( X24 = X23 )
      | ( r2_hidden @ X23 @ X24 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('72',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ ( k3_tarski @ X15 ) )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ X1 ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( r1_tarski @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( ( sk_B @ ( k3_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ( ( sk_B @ ( k3_tarski @ X0 ) )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k3_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ ( sk_B @ ( k3_tarski @ X0 ) ) )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('86',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( ( sk_B @ ( k3_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ X0 )
      | ( ( sk_B @ ( k3_tarski @ X0 ) )
        = X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( v1_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( sk_B @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B @ X0 ) )
      | ( v1_ordinal1 @ ( k3_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_ordinal1 @ ( sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ ( k3_tarski @ sk_A ) ) )
    | ~ ( v1_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) )
    | ( v1_ordinal1 @ ( k3_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','110'])).

thf('112',plain,(
    v3_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('114',plain,(
    v1_ordinal1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ ( k3_tarski @ sk_A ) ) )
    | ( v1_ordinal1 @ ( k3_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,(
    ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','39'])).

thf('117',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) )
    | ( r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ ( k3_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('119',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ ( sk_D_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('122',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_D_1 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v1_ordinal1 @ ( k3_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) )
    | ( r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','134'])).

thf('136',plain,(
    ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','39'])).

thf('137',plain,
    ( ~ ( v1_ordinal1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('139',plain,(
    r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ ( sk_D_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('141',plain,(
    r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('143',plain,
    ( ~ ( v1_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) )
    | ( r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    r2_hidden @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('145',plain,(
    ! [X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k3_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('146',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X25: $i] :
      ( ( v3_ordinal1 @ X25 )
      | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v3_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('150',plain,(
    v1_ordinal1 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['143','150'])).

thf('152',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','153'])).

thf('155',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['144','145'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('159',plain,
    ( ( r1_tarski @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    r1_tarski @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( sk_B @ ( k3_tarski @ sk_A ) ) ) @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['154','162'])).

thf('164',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('165',plain,
    ( ( r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    r1_tarski @ ( sk_B @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( r1_tarski @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('168',plain,(
    v1_ordinal1 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['40','168'])).


%------------------------------------------------------------------------------
