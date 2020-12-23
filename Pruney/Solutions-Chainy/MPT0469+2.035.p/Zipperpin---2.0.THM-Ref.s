%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nMICQgOz1R

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:21 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 253 expanded)
%              Number of leaves         :   33 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  636 (1656 expanded)
%              Number of equality atoms :   66 ( 167 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X40: $i] :
      ( ( X40
        = ( k1_relat_1 @ X37 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ X40 @ X37 ) @ ( sk_D_1 @ X40 @ X37 ) ) @ X37 )
      | ( r2_hidden @ ( sk_C_3 @ X40 @ X37 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X22 )
      | ( ( k4_xboole_0 @ X20 @ X22 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X45: $i] :
      ( ( ( k1_relat_1 @ X45 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X44: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('29',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X22 )
      | ( ( k4_xboole_0 @ X20 @ X22 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('43',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_relat_1 @ X1 )
         != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','37'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('57',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['47','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['40','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','59'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X43: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','37'])).

thf('65',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('66',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ X32 )
      | ( r2_hidden @ ( sk_B_2 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['63','64','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nMICQgOz1R
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/1.00  % Solved by: fo/fo7.sh
% 0.79/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.00  % done 2148 iterations in 0.538s
% 0.79/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/1.00  % SZS output start Refutation
% 0.79/1.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.79/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/1.00  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.79/1.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.79/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/1.00  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.79/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/1.00  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.79/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/1.00  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.79/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/1.00  thf(sk_B_type, type, sk_B: $i > $i).
% 0.79/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.00  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.79/1.00  thf(d4_relat_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.79/1.00       ( ![C:$i]:
% 0.79/1.00         ( ( r2_hidden @ C @ B ) <=>
% 0.79/1.00           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.79/1.00  thf('0', plain,
% 0.79/1.00      (![X37 : $i, X40 : $i]:
% 0.79/1.00         (((X40) = (k1_relat_1 @ X37))
% 0.79/1.00          | (r2_hidden @ 
% 0.79/1.00             (k4_tarski @ (sk_C_3 @ X40 @ X37) @ (sk_D_1 @ X40 @ X37)) @ X37)
% 0.79/1.00          | (r2_hidden @ (sk_C_3 @ X40 @ X37) @ X40))),
% 0.79/1.00      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.79/1.00  thf(t46_xboole_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.79/1.00  thf('1', plain,
% 0.79/1.00      (![X18 : $i, X19 : $i]:
% 0.79/1.00         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.79/1.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.79/1.00  thf(t83_xboole_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/1.00  thf('2', plain,
% 0.79/1.00      (![X20 : $i, X22 : $i]:
% 0.79/1.00         ((r1_xboole_0 @ X20 @ X22) | ((k4_xboole_0 @ X20 @ X22) != (X20)))),
% 0.79/1.00      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.79/1.00  thf('3', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (((k1_xboole_0) != (X0))
% 0.79/1.00          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.79/1.00  thf('4', plain,
% 0.79/1.00      (![X1 : $i]:
% 0.79/1.00         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.79/1.00      inference('simplify', [status(thm)], ['3'])).
% 0.79/1.00  thf('5', plain,
% 0.79/1.00      (![X18 : $i, X19 : $i]:
% 0.79/1.00         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.79/1.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.79/1.00  thf(l32_xboole_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.79/1.00  thf('6', plain,
% 0.79/1.00      (![X12 : $i, X13 : $i]:
% 0.79/1.00         ((r1_tarski @ X12 @ X13)
% 0.79/1.00          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.79/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.79/1.00  thf('7', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (((k1_xboole_0) != (k1_xboole_0))
% 0.79/1.00          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['5', '6'])).
% 0.79/1.00  thf('8', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.79/1.00      inference('simplify', [status(thm)], ['7'])).
% 0.79/1.00  thf(t28_xboole_1, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.79/1.00  thf('9', plain,
% 0.79/1.00      (![X16 : $i, X17 : $i]:
% 0.79/1.00         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.79/1.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/1.00  thf('10', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.79/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.79/1.00  thf(t4_xboole_0, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.79/1.00            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.79/1.00       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.79/1.00            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.79/1.00  thf('11', plain,
% 0.79/1.00      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.79/1.00          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.79/1.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.79/1.00  thf('12', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X2 @ X0)
% 0.79/1.00          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['10', '11'])).
% 0.79/1.00  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.79/1.00      inference('sup-', [status(thm)], ['4', '12'])).
% 0.79/1.00  thf('14', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.79/1.00          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['0', '13'])).
% 0.79/1.00  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.79/1.00      inference('sup-', [status(thm)], ['4', '12'])).
% 0.79/1.00  thf('16', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/1.00  thf(t37_relat_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( v1_relat_1 @ A ) =>
% 0.79/1.00       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.79/1.00         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.79/1.00  thf('17', plain,
% 0.79/1.00      (![X45 : $i]:
% 0.79/1.00         (((k1_relat_1 @ X45) = (k2_relat_1 @ (k4_relat_1 @ X45)))
% 0.79/1.00          | ~ (v1_relat_1 @ X45))),
% 0.79/1.00      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.79/1.00  thf(t7_xboole_0, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.79/1.00          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.79/1.00  thf('18', plain,
% 0.79/1.00      (![X11 : $i]:
% 0.79/1.00         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.79/1.00      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.79/1.00  thf(d1_xboole_0, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.79/1.00  thf('19', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.79/1.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.00  thf('20', plain,
% 0.79/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['18', '19'])).
% 0.79/1.00  thf(t1_boole, axiom,
% 0.79/1.00    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/1.00  thf('21', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.79/1.00      inference('cnf', [status(esa)], [t1_boole])).
% 0.79/1.00  thf('22', plain,
% 0.79/1.00      (![X18 : $i, X19 : $i]:
% 0.79/1.00         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 0.79/1.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.79/1.00  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['21', '22'])).
% 0.79/1.00  thf('24', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (((k4_xboole_0 @ X1 @ X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['20', '23'])).
% 0.79/1.00  thf(fc9_relat_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.79/1.00       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.79/1.00  thf('25', plain,
% 0.79/1.00      (![X44 : $i]:
% 0.79/1.00         (~ (v1_xboole_0 @ (k2_relat_1 @ X44))
% 0.79/1.00          | ~ (v1_relat_1 @ X44)
% 0.79/1.00          | (v1_xboole_0 @ X44))),
% 0.79/1.00      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.79/1.00  thf('26', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 0.79/1.00          | ~ (v1_xboole_0 @ (k2_relat_1 @ X1))
% 0.79/1.00          | (v1_xboole_0 @ X1)
% 0.79/1.00          | ~ (v1_relat_1 @ X1))),
% 0.79/1.00      inference('sup-', [status(thm)], ['24', '25'])).
% 0.79/1.00  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['21', '22'])).
% 0.79/1.00  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['21', '22'])).
% 0.79/1.00  thf('29', plain,
% 0.79/1.00      (![X20 : $i, X22 : $i]:
% 0.79/1.00         ((r1_xboole_0 @ X20 @ X22) | ((k4_xboole_0 @ X20 @ X22) != (X20)))),
% 0.79/1.00      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.79/1.00  thf('30', plain,
% 0.79/1.00      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['28', '29'])).
% 0.79/1.00  thf('31', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.79/1.00      inference('simplify', [status(thm)], ['30'])).
% 0.79/1.00  thf('32', plain,
% 0.79/1.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.79/1.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.00  thf('33', plain,
% 0.79/1.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.79/1.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.00  thf(t3_xboole_0, axiom,
% 0.79/1.00    (![A:$i,B:$i]:
% 0.79/1.00     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.79/1.00            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.79/1.00       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.79/1.00            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.79/1.00  thf('34', plain,
% 0.79/1.00      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X5 @ X3)
% 0.79/1.00          | ~ (r2_hidden @ X5 @ X6)
% 0.79/1.00          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.79/1.00      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.79/1.00  thf('35', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         ((v1_xboole_0 @ X0)
% 0.79/1.00          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.79/1.00          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.79/1.00      inference('sup-', [status(thm)], ['33', '34'])).
% 0.79/1.00  thf('36', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['32', '35'])).
% 0.79/1.00  thf('37', plain,
% 0.79/1.00      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('simplify', [status(thm)], ['36'])).
% 0.79/1.00  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/1.00      inference('sup-', [status(thm)], ['31', '37'])).
% 0.79/1.00  thf('39', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['27', '38'])).
% 0.79/1.00  thf('40', plain,
% 0.79/1.00      (![X1 : $i]:
% 0.79/1.00         (~ (v1_xboole_0 @ (k2_relat_1 @ X1))
% 0.79/1.00          | (v1_xboole_0 @ X1)
% 0.79/1.00          | ~ (v1_relat_1 @ X1))),
% 0.79/1.00      inference('demod', [status(thm)], ['26', '39'])).
% 0.79/1.00  thf('41', plain,
% 0.79/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['18', '19'])).
% 0.79/1.00  thf('42', plain,
% 0.79/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['18', '19'])).
% 0.79/1.00  thf(t60_relat_1, conjecture,
% 0.79/1.00    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.79/1.00     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.79/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.00    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.79/1.00        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.79/1.00    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.79/1.00  thf('43', plain,
% 0.79/1.00      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.79/1.00        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.79/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.00  thf('44', plain,
% 0.79/1.00      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.79/1.00         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('split', [status(esa)], ['43'])).
% 0.79/1.00  thf('45', plain,
% 0.79/1.00      ((![X0 : $i]:
% 0.79/1.00          (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.79/1.00         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['42', '44'])).
% 0.79/1.00  thf('46', plain,
% 0.79/1.00      ((![X0 : $i, X1 : $i]:
% 0.79/1.00          (((k2_relat_1 @ X1) != (X0))
% 0.79/1.00           | ~ (v1_xboole_0 @ X0)
% 0.79/1.00           | ~ (v1_xboole_0 @ X1)))
% 0.79/1.00         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['41', '45'])).
% 0.79/1.00  thf('47', plain,
% 0.79/1.00      ((![X1 : $i]:
% 0.79/1.00          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1))))
% 0.79/1.00         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('simplify', [status(thm)], ['46'])).
% 0.79/1.00  thf('48', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/1.00  thf('49', plain,
% 0.79/1.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['18', '19'])).
% 0.79/1.00  thf('50', plain,
% 0.79/1.00      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.79/1.00         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('split', [status(esa)], ['43'])).
% 0.79/1.00  thf('51', plain,
% 0.79/1.00      ((![X0 : $i]:
% 0.79/1.00          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.79/1.00         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['49', '50'])).
% 0.79/1.00  thf('52', plain,
% 0.79/1.00      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.79/1.00         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('sup-', [status(thm)], ['48', '51'])).
% 0.79/1.00  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/1.00      inference('sup-', [status(thm)], ['31', '37'])).
% 0.79/1.00  thf('54', plain,
% 0.79/1.00      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.79/1.00         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.79/1.00      inference('demod', [status(thm)], ['52', '53'])).
% 0.79/1.00  thf('55', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.79/1.00      inference('simplify', [status(thm)], ['54'])).
% 0.79/1.00  thf('56', plain,
% 0.79/1.00      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.79/1.00       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.79/1.00      inference('split', [status(esa)], ['43'])).
% 0.79/1.00  thf('57', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.79/1.00      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.79/1.00  thf('58', plain,
% 0.79/1.00      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1)))),
% 0.79/1.00      inference('simpl_trail', [status(thm)], ['47', '57'])).
% 0.79/1.00  thf('59', plain,
% 0.79/1.00      (![X1 : $i]: (~ (v1_relat_1 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1)))),
% 0.79/1.00      inference('clc', [status(thm)], ['40', '58'])).
% 0.79/1.00  thf('60', plain,
% 0.79/1.00      (![X0 : $i]:
% 0.79/1.00         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.79/1.00          | ~ (v1_relat_1 @ X0)
% 0.79/1.00          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.79/1.00      inference('sup-', [status(thm)], ['17', '59'])).
% 0.79/1.00  thf(dt_k4_relat_1, axiom,
% 0.79/1.00    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.79/1.00  thf('61', plain,
% 0.79/1.00      (![X43 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X43)) | ~ (v1_relat_1 @ X43))),
% 0.79/1.00      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.79/1.00  thf('62', plain,
% 0.79/1.00      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.79/1.00      inference('clc', [status(thm)], ['60', '61'])).
% 0.79/1.00  thf('63', plain,
% 0.79/1.00      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['16', '62'])).
% 0.79/1.00  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/1.00      inference('sup-', [status(thm)], ['31', '37'])).
% 0.79/1.00  thf('65', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.79/1.00      inference('simplify', [status(thm)], ['30'])).
% 0.79/1.00  thf(d1_relat_1, axiom,
% 0.79/1.00    (![A:$i]:
% 0.79/1.00     ( ( v1_relat_1 @ A ) <=>
% 0.79/1.00       ( ![B:$i]:
% 0.79/1.00         ( ~( ( r2_hidden @ B @ A ) & 
% 0.79/1.00              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.79/1.00  thf('66', plain,
% 0.79/1.00      (![X32 : $i]: ((v1_relat_1 @ X32) | (r2_hidden @ (sk_B_2 @ X32) @ X32))),
% 0.79/1.00      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.79/1.00  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/1.00      inference('sup+', [status(thm)], ['21', '22'])).
% 0.79/1.00  thf('68', plain,
% 0.79/1.00      (![X12 : $i, X13 : $i]:
% 0.79/1.00         ((r1_tarski @ X12 @ X13)
% 0.79/1.00          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.79/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.79/1.00  thf('69', plain,
% 0.79/1.00      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['67', '68'])).
% 0.79/1.00  thf('70', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.79/1.00      inference('simplify', [status(thm)], ['69'])).
% 0.79/1.00  thf('71', plain,
% 0.79/1.00      (![X16 : $i, X17 : $i]:
% 0.79/1.00         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.79/1.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.79/1.00  thf('72', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['70', '71'])).
% 0.79/1.00  thf('73', plain,
% 0.79/1.00      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.79/1.00          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.79/1.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.79/1.00  thf('74', plain,
% 0.79/1.00      (![X0 : $i, X1 : $i]:
% 0.79/1.00         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['72', '73'])).
% 0.79/1.00  thf('75', plain,
% 0.79/1.00      (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.79/1.00      inference('sup-', [status(thm)], ['66', '74'])).
% 0.79/1.00  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.79/1.00      inference('sup-', [status(thm)], ['65', '75'])).
% 0.79/1.00  thf('77', plain, ($false),
% 0.79/1.00      inference('demod', [status(thm)], ['63', '64', '76'])).
% 0.79/1.00  
% 0.79/1.00  % SZS output end Refutation
% 0.79/1.00  
% 0.79/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
