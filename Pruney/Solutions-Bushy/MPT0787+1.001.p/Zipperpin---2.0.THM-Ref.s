%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SLttG6aA8T

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 767 expanded)
%              Number of leaves         :   24 ( 209 expanded)
%              Depth                    :   28
%              Number of atoms          : 1148 (11494 expanded)
%              Number of equality atoms :   36 ( 197 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( X5 = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( X4 != X1 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
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
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 ) ) ),
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
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
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
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ~ ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X9 ) ) ),
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
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ~ ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X9 ) ) ),
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
