%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k3pxDWimW1

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:33 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 767 expanded)
%              Number of leaves         :   24 ( 209 expanded)
%              Depth                    :   28
%              Number of atoms          : 1148 (11494 expanded)
%              Number of equality atoms :   36 ( 197 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t37_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
         => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
          <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_wellord1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_B_4 @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v6_relat_2 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k3_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X21 ) @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X20 )
      | ( X21 = X22 )
      | ~ ( r2_hidden @ X22 @ ( k3_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_4 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_4 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_4 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_4 )
      | ~ ( v6_relat_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('10',plain,
    ( ( v6_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_4 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_4 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_4 @ sk_A ) @ sk_C_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ( sk_A = sk_B_4 ) ),
    inference('sup-',[status(thm)],['3','13'])).

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

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( X9 = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( X9 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( r2_hidden @ X9 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A = sk_B_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ( r2_hidden @ sk_B_4 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_B_4 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = sk_B_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ( r2_hidden @ sk_B_4 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_B_4 = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B_4 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ( sk_A = sk_B_4 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_4 )
      | ( r2_hidden @ sk_B_4 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(split,[status(esa)],['23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_A = sk_B_4 )
      | ( r2_hidden @ sk_B_4 @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( X8 != X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_A = sk_B_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = sk_B_4 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_4 )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
      & ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_2 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_4 )
    | ~ ( v1_relat_2 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v1_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('41',plain,
    ( ( v1_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C_4 ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ) ),
    inference(split,[status(esa)],['23'])).

thf('49',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('50',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ),
    inference('sat_resolution*',[status(thm)],['2','45','49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v8_relat_2 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_4 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ sk_B_4 ) @ sk_C_4 )
      | ~ ( v8_relat_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v8_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('63',plain,
    ( ( v8_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v8_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ sk_B_4 ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['59','60','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( X9 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( r2_hidden @ X9 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
        = sk_B_4 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
        = sk_B_4 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      = sk_B_4 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      = sk_B_4 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('75',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    = sk_B_4 ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v4_relat_2 @ X17 )
      | ( X19 = X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( v4_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( X1
        = ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ( sk_A
      = ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) )
    | ~ ( v4_relat_2 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_4 ) @ sk_C_4 ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    = sk_B_4 ),
    inference(clc,[status(thm)],['73','74'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v4_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('86',plain,
    ( ( v4_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v4_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) )
    | ( sk_A = sk_B_4 ) ),
    inference(demod,[status(thm)],['80','81','82','83','88'])).

thf('90',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_4 ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('91',plain,(
    sk_A = sk_B_4 ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['47','91','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k3pxDWimW1
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 152 iterations in 0.193s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.66  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.47/0.66  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.47/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.66  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(sk_B_4_type, type, sk_B_4: $i).
% 0.47/0.66  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.47/0.66  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.47/0.66  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.47/0.66  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.47/0.66  thf(t37_wellord1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ C ) =>
% 0.47/0.66       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.47/0.66           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.47/0.66         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.47/0.66           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ( v1_relat_1 @ C ) =>
% 0.47/0.66          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.47/0.66              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.47/0.66            ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.47/0.66              ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t37_wellord1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66           (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66           (k1_wellord1 @ sk_C_4 @ sk_B_4)))
% 0.47/0.66         <= (~
% 0.47/0.66             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (~
% 0.47/0.66       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4))) | 
% 0.47/0.66       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('3', plain, ((r2_hidden @ sk_B_4 @ (k3_relat_1 @ sk_C_4))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('4', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(l4_wellord1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( v6_relat_2 @ A ) <=>
% 0.47/0.66         ( ![B:$i,C:$i]:
% 0.47/0.66           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.47/0.66                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.47/0.66                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.47/0.66                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.66         (~ (v6_relat_2 @ X20)
% 0.47/0.66          | ~ (r2_hidden @ X21 @ (k3_relat_1 @ X20))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X22 @ X21) @ X20)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X21 @ X22) @ X20)
% 0.47/0.66          | ((X21) = (X22))
% 0.47/0.66          | ~ (r2_hidden @ X22 @ (k3_relat_1 @ X20))
% 0.47/0.66          | ~ (v1_relat_1 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ sk_C_4)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 0.47/0.66          | ((sk_A) = (X0))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4)
% 0.47/0.66          | ~ (v6_relat_2 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf('7', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('8', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d4_wellord1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( v2_wellord1 @ A ) <=>
% 0.47/0.66         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.47/0.66           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (~ (v2_wellord1 @ X10) | (v6_relat_2 @ X10) | ~ (v1_relat_1 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.47/0.66  thf('10', plain, (((v6_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain, ((v2_wellord1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('12', plain, ((v6_relat_2 @ sk_C_4)),
% 0.47/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 0.47/0.66          | ((sk_A) = (X0))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4))),
% 0.47/0.66      inference('demod', [status(thm)], ['6', '7', '12'])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (((r2_hidden @ (k4_tarski @ sk_B_4 @ sk_A) @ sk_C_4)
% 0.47/0.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)
% 0.47/0.66        | ((sk_A) = (sk_B_4)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '13'])).
% 0.47/0.66  thf(d1_wellord1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i,C:$i]:
% 0.47/0.66         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.47/0.66           ( ![D:$i]:
% 0.47/0.66             ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.66               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.47/0.66         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.47/0.66          | (r2_hidden @ X9 @ X7)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.47/0.66          | ((X9) = (X5))
% 0.47/0.66          | ~ (v1_relat_1 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X6)
% 0.47/0.66          | ((X9) = (X5))
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.47/0.66          | (r2_hidden @ X9 @ (k1_wellord1 @ X6 @ X5)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['15'])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      ((((sk_A) = (sk_B_4))
% 0.47/0.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)
% 0.47/0.66        | (r2_hidden @ sk_B_4 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.47/0.66        | ((sk_B_4) = (sk_A))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '16'])).
% 0.47/0.66  thf('18', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      ((((sk_A) = (sk_B_4))
% 0.47/0.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)
% 0.47/0.66        | (r2_hidden @ sk_B_4 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.47/0.66        | ((sk_B_4) = (sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (((r2_hidden @ sk_B_4 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.47/0.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)
% 0.47/0.66        | ((sk_A) = (sk_B_4)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (((((sk_A) = (sk_B_4))
% 0.47/0.66         | (r2_hidden @ sk_B_4 @ (k1_wellord1 @ sk_C_4 @ sk_A))))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4)))
% 0.47/0.66         <= (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('split', [status(esa)], ['23'])).
% 0.47/0.66  thf(d3_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ X0 @ X2)
% 0.47/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r2_hidden @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66           | ~ (r2_hidden @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A))))
% 0.47/0.66         <= (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (((((sk_A) = (sk_B_4))
% 0.47/0.66         | (r2_hidden @ sk_B_4 @ (k1_wellord1 @ sk_C_4 @ sk_B_4))))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)) & 
% 0.47/0.66             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '26'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.66         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.47/0.66          | ((X8) != (X5))
% 0.47/0.66          | ~ (r2_hidden @ X8 @ X7)
% 0.47/0.66          | ~ (v1_relat_1 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X6) | ~ (r2_hidden @ X5 @ (k1_wellord1 @ X6 @ X5)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (((((sk_A) = (sk_B_4)) | ~ (v1_relat_1 @ sk_C_4)))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)) & 
% 0.47/0.66             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '29'])).
% 0.47/0.66  thf('31', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      ((((sk_A) = (sk_B_4)))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)) & 
% 0.47/0.66             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)))),
% 0.47/0.66      inference('split', [status(esa)], ['0'])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_4))
% 0.47/0.66         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)) & 
% 0.47/0.66             ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_B_4))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(l1_wellord1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( v1_relat_2 @ A ) <=>
% 0.47/0.66         ( ![B:$i]:
% 0.47/0.66           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.47/0.66             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i]:
% 0.47/0.66         (~ (v1_relat_2 @ X11)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X12 @ X12) @ X11)
% 0.47/0.66          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X11))
% 0.47/0.66          | ~ (v1_relat_1 @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_C_4)
% 0.47/0.66        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_4)
% 0.47/0.66        | ~ (v1_relat_2 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.66  thf('38', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('39', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (~ (v2_wellord1 @ X10) | (v1_relat_2 @ X10) | ~ (v1_relat_1 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.47/0.66  thf('41', plain, (((v1_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.66  thf('42', plain, ((v2_wellord1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('43', plain, ((v1_relat_2 @ sk_C_4)),
% 0.47/0.66      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf('44', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C_4)),
% 0.47/0.66      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)) | 
% 0.47/0.66       ~
% 0.47/0.66       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4)))),
% 0.47/0.66      inference('demod', [status(thm)], ['34', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (~
% 0.47/0.66       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66          (k1_wellord1 @ sk_C_4 @ sk_B_4))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))
% 0.47/0.66         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)))),
% 0.47/0.66      inference('split', [status(esa)], ['23'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)) | 
% 0.47/0.66       ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4)))),
% 0.47/0.66      inference('split', [status(esa)], ['23'])).
% 0.47/0.66  thf('50', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['2', '45', '49'])).
% 0.47/0.66  thf('51', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.66         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X8 @ X5) @ X6)
% 0.47/0.66          | ~ (r2_hidden @ X8 @ X7)
% 0.47/0.66          | ~ (v1_relat_1 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X6)
% 0.47/0.66          | ~ (r2_hidden @ X8 @ (k1_wellord1 @ X6 @ X5))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X8 @ X5) @ X6))),
% 0.47/0.66      inference('simplify', [status(thm)], ['53'])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['52', '54'])).
% 0.47/0.66  thf(l2_wellord1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( v8_relat_2 @ A ) <=>
% 0.47/0.66         ( ![B:$i,C:$i,D:$i]:
% 0.47/0.66           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.47/0.66               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 0.47/0.66             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         (~ (v8_relat_2 @ X13)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X13)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ X13)
% 0.47/0.66          | ~ (v1_relat_1 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [l2_wellord1])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 0.47/0.66          | ~ (v8_relat_2 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         (~ (v8_relat_2 @ X0)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 0.47/0.66          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ sk_C_4)
% 0.47/0.66          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ sk_B_4) @ 
% 0.47/0.66             sk_C_4)
% 0.47/0.66          | ~ (v8_relat_2 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '58'])).
% 0.47/0.66  thf('60', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('61', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (~ (v2_wellord1 @ X10) | (v8_relat_2 @ X10) | ~ (v1_relat_1 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.47/0.66  thf('63', plain, (((v8_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.66  thf('64', plain, ((v2_wellord1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('65', plain, ((v8_relat_2 @ sk_C_4)),
% 0.47/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ sk_B_4) @ 
% 0.47/0.66             sk_C_4))),
% 0.47/0.66      inference('demod', [status(thm)], ['59', '60', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X6)
% 0.47/0.66          | ((X9) = (X5))
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.47/0.66          | (r2_hidden @ X9 @ (k1_wellord1 @ X6 @ X5)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['15'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 0.47/0.66          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 0.47/0.66             (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_4))
% 0.47/0.66          | ~ (v1_relat_1 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.47/0.66  thf('69', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('70', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 0.47/0.66          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 0.47/0.66             (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_4)))),
% 0.47/0.66      inference('demod', [status(thm)], ['68', '69'])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      ((((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_4) @ 
% 0.47/0.66          (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_4))
% 0.47/0.66        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66           (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66           (k1_wellord1 @ sk_C_4 @ sk_B_4)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['70', '71'])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66        | ((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_4) @ 
% 0.47/0.66            (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_4)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['72'])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      (~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66          (k1_wellord1 @ sk_C_4 @ sk_B_4))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      (((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_4) @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.47/0.66         = (sk_B_4))),
% 0.47/0.66      inference('clc', [status(thm)], ['73', '74'])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['52', '54'])).
% 0.47/0.66  thf(l3_wellord1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( v4_relat_2 @ A ) <=>
% 0.47/0.66         ( ![B:$i,C:$i]:
% 0.47/0.66           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.47/0.66               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 0.47/0.66             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (v4_relat_2 @ X17)
% 0.47/0.66          | ((X19) = (X18))
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X17)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X17)
% 0.47/0.66          | ~ (v1_relat_1 @ X17))),
% 0.47/0.66      inference('cnf', [status(esa)], [l3_wellord1])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X0)
% 0.47/0.66          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.47/0.66          | ~ (v1_relat_1 @ X0)
% 0.47/0.66          | ~ (r2_hidden @ 
% 0.47/0.66               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 0.47/0.66          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 0.47/0.66          | ~ (v4_relat_2 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (v4_relat_2 @ X0)
% 0.47/0.66          | ((X1) = (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)))
% 0.47/0.66          | ~ (r2_hidden @ 
% 0.47/0.66               (k4_tarski @ X1 @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1))) @ X0)
% 0.47/0.66          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.47/0.66          | ~ (v1_relat_1 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['78'])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C_4)
% 0.47/0.66        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66           (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66        | ((sk_A)
% 0.47/0.66            = (sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_4) @ 
% 0.47/0.66               (k1_wellord1 @ sk_C_4 @ sk_A)))
% 0.47/0.66        | ~ (v4_relat_2 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['75', '79'])).
% 0.47/0.66  thf('81', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_4) @ sk_C_4)),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.47/0.66  thf('82', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      (((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_4) @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 0.47/0.66         = (sk_B_4))),
% 0.47/0.66      inference('clc', [status(thm)], ['73', '74'])).
% 0.47/0.66  thf('84', plain, ((v1_relat_1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (~ (v2_wellord1 @ X10) | (v4_relat_2 @ X10) | ~ (v1_relat_1 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.47/0.66  thf('86', plain, (((v4_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 0.47/0.66      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.66  thf('87', plain, ((v2_wellord1 @ sk_C_4)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('88', plain, ((v4_relat_2 @ sk_C_4)),
% 0.47/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.66  thf('89', plain,
% 0.47/0.66      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66         (k1_wellord1 @ sk_C_4 @ sk_B_4))
% 0.47/0.66        | ((sk_A) = (sk_B_4)))),
% 0.47/0.66      inference('demod', [status(thm)], ['80', '81', '82', '83', '88'])).
% 0.47/0.66  thf('90', plain,
% 0.47/0.66      (~ (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 0.47/0.66          (k1_wellord1 @ sk_C_4 @ sk_B_4))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.47/0.66  thf('91', plain, (((sk_A) = (sk_B_4))),
% 0.47/0.66      inference('clc', [status(thm)], ['89', '90'])).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('94', plain,
% 0.47/0.66      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.66  thf('95', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['94'])).
% 0.47/0.66  thf('96', plain, ($false),
% 0.47/0.66      inference('demod', [status(thm)], ['47', '91', '95'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
