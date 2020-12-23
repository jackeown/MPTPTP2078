%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0761+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bFpnh9HZJC

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 267 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   24
%              Number of atoms          :  759 (2657 expanded)
%              Number of equality atoms :   34 (  92 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_wellord1_type,type,(
    r1_wellord1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t5_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_wellord1 @ A )
      <=> ( r1_wellord1 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v1_wellord1 @ A )
        <=> ( r1_wellord1 @ A @ ( k3_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_wellord1])).

thf('0',plain,
    ( ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_wellord1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_wellord1 @ A )
      <=> ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ( r1_xboole_0 @ ( k1_wellord1 @ A @ C ) @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('4',plain,
    ( ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
    | ( v1_wellord1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_wellord1 @ A @ B )
        <=> ! [C: $i] :
              ~ ( ( r1_tarski @ C @ B )
                & ( C != k1_xboole_0 )
                & ! [D: $i] :
                    ~ ( ( r2_hidden @ D @ C )
                      & ( r1_xboole_0 @ ( k1_wellord1 @ A @ D ) @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ~ ( r1_wellord1 @ X3 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( X7 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_wellord1 @ X3 @ ( sk_D @ X7 @ X3 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_wellord1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ( r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
        | ( X0 = k1_xboole_0 )
        | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_D @ X0 @ sk_A ) ) @ X0 )
        | ( X0 = k1_xboole_0 )
        | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v1_wellord1 @ sk_A )
      | ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) ) @ ( sk_B @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( v1_wellord1 @ sk_A )
      | ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) ) @ ( sk_B @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_wellord1 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('14',plain,
    ( ( ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v1_wellord1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( v1_wellord1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v1_wellord1 @ sk_A )
      | ( v1_wellord1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) )
      | ( v1_wellord1 @ sk_A )
      | ( ( sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('19',plain,
    ( ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ~ ( r1_wellord1 @ X3 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 ) @ X7 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_wellord1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_A ) @ X0 )
        | ( X0 = k1_xboole_0 )
        | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_A ) @ X0 )
        | ( X0 = k1_xboole_0 )
        | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v1_wellord1 @ sk_A )
      | ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( v1_wellord1 @ sk_A )
      | ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( ( sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v1_wellord1 @ sk_A ) )
   <= ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','26'])).

thf('28',plain,
    ( ~ ( v1_wellord1 @ sk_A )
   <= ~ ( v1_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( v1_wellord1 @ sk_A )
      & ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != k1_xboole_0 )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( v1_wellord1 @ sk_A ) )
   <= ( ~ ( v1_wellord1 @ sk_A )
      & ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_wellord1 @ sk_A ) )
   <= ( ~ ( v1_wellord1 @ sk_A )
      & ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_wellord1 @ sk_A )
   <= ( ~ ( v1_wellord1 @ sk_A )
      & ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_wellord1 @ sk_A )
   <= ~ ( v1_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( v1_wellord1 @ sk_A )
    | ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','36'])).

thf('38',plain,(
    ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X5 @ X3 ) @ X5 )
      | ( r1_wellord1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_wellord1])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_wellord1 @ X0 )
      | ~ ( r1_tarski @ X2 @ ( k3_relat_1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_wellord1 @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X1 ) @ X0 ) @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X1 ) )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X5 @ X3 ) @ X5 )
      | ( r1_wellord1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_wellord1])).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_wellord1 @ X0 )
      | ~ ( r1_tarski @ X2 @ ( k3_relat_1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_wellord1 @ X0 @ ( sk_C @ X2 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_wellord1 @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_wellord1 @ X0 @ ( sk_C @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X1 ) @ X0 ) ) @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X1 ) )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_wellord1 @ X3 @ X4 ) @ ( sk_C_1 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X4 @ ( sk_C_1 @ X5 @ X3 ) )
      | ( r1_wellord1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_wellord1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_wellord1 @ X0 )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) )
      | ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_wellord1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_wellord1 @ X0 )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_wellord1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('51',plain,
    ( ~ ( v1_wellord1 @ sk_A )
    | ( ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_wellord1 @ sk_A )
   <= ( v1_wellord1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ( v1_wellord1 @ sk_A )
    | ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('54',plain,(
    v1_wellord1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','36','53'])).

thf('55',plain,(
    v1_wellord1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_C_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55','56'])).

thf('58',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( sk_C_1 @ X5 @ X3 )
       != k1_xboole_0 )
      | ( r1_wellord1 @ X3 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_wellord1])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    r1_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['38','62'])).


%------------------------------------------------------------------------------
