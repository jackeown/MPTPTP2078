%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AZzPcxMkgG

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:09 EST 2020

% Result     : Theorem 7.30s
% Output     : Refutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 432 expanded)
%              Number of leaves         :   29 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          : 1415 (4076 expanded)
%              Number of equality atoms :   29 (  54 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_ordinal1_type,type,(
    v4_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t41_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v4_ordinal1 @ A )
      <=> ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ B @ A )
             => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( ( v4_ordinal1 @ A )
        <=> ! [B: $i] :
              ( ( v3_ordinal1 @ B )
             => ( ( r2_hidden @ B @ A )
               => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_ordinal1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X39: $i] :
      ( ~ ( v3_ordinal1 @ X39 )
      | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
      | ~ ( r2_hidden @ X39 @ sk_A )
      | ( v4_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t35_ordinal1,axiom,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( v3_ordinal1 @ B ) )
     => ( v3_ordinal1 @ ( k3_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X35 ) )
      | ( r2_hidden @ ( sk_B_1 @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v3_ordinal1 @ X26 )
      | ~ ( v3_ordinal1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X35: $i] :
      ( ( v3_ordinal1 @ ( k3_tarski @ X35 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t35_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v3_ordinal1 @ X26 )
      | ~ ( v3_ordinal1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ~ ( v3_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_ordinal1 @ sk_A )
        | ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_ordinal1 @ ( sk_C @ X0 @ sk_A ) ) @ sk_A )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('19',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ( r2_hidden @ X29 @ X28 )
      | ( X29 = X28 )
      | ( r2_hidden @ X28 @ X29 )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( ( k3_tarski @ sk_A )
        = sk_A )
      | ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_A )
      | ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( ( k3_tarski @ sk_A )
        = sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( ( k3_tarski @ sk_A )
        = sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('37',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('40',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_A )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('42',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('43',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_A )
      | ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ( r2_hidden @ sk_A @ ( k3_tarski @ sk_A ) )
      | ( ( k3_tarski @ sk_A )
        = sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X8 ) )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('47',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_A )
      | ( r2_hidden @ sk_A @ ( sk_D_1 @ sk_A @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,
    ( ( ( ( k3_tarski @ sk_A )
        = sk_A )
      | ~ ( r1_tarski @ ( sk_D_1 @ sk_A @ sk_A ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k3_tarski @ sk_A )
      = sk_A )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','50'])).

thf(d6_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v4_ordinal1 @ A )
    <=> ( A
        = ( k3_tarski @ A ) ) ) )).

thf('52',plain,(
    ! [X22: $i] :
      ( ( v4_ordinal1 @ X22 )
      | ( X22
       != ( k3_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('53',plain,
    ( ( ( sk_A != sk_A )
      | ( v4_ordinal1 @ sk_A ) )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ! [X39: $i] :
        ( ~ ( v3_ordinal1 @ X39 )
        | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
        | ~ ( r2_hidden @ X39 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v4_ordinal1 @ sk_A )
   <= ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ~ ! [X39: $i] :
          ( ~ ( v3_ordinal1 @ X39 )
          | ( r2_hidden @ ( k1_ordinal1 @ X39 ) @ sk_A )
          | ~ ( r2_hidden @ X39 @ sk_A ) )
    | ( v4_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('59',plain,(
    ! [X30: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X30 ) )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('60',plain,(
    ! [X30: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X30 ) )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('61',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('62',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X32 ) @ X31 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('63',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_3 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v3_ordinal1 @ X26 )
      | ~ ( v3_ordinal1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('66',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ sk_B_3 ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['63','68','69'])).

thf(t34_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf('71',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v3_ordinal1 @ X33 )
      | ~ ( r1_ordinal1 @ X34 @ X33 )
      | ( r2_hidden @ X34 @ ( k1_ordinal1 @ X33 ) )
      | ~ ( v3_ordinal1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t34_ordinal1])).

thf('72',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ ( k1_ordinal1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_3 )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','74'])).

thf('76',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('77',plain,
    ( ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ ( k1_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v3_ordinal1 @ X26 )
      | ~ ( v3_ordinal1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('79',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ( r2_hidden @ X29 @ X28 )
      | ( X29 = X28 )
      | ( r2_hidden @ X28 @ X29 )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('85',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) )
      | ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A ) )
   <= ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('90',plain,
    ( ( ( ( k1_ordinal1 @ sk_B_3 )
        = sk_A )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X30: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X30 ) )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('92',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['63','68','69'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('93',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('94',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_3 )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('99',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_ordinal1 @ sk_B_3 )
      = sk_A )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('102',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,(
    ! [X21: $i] :
      ( ( X21
        = ( k3_tarski @ X21 ) )
      | ~ ( v4_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('104',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ ( sk_D_1 @ X11 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( r2_hidden @ sk_B_3 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( r2_hidden @ sk_B_3 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X32 ) @ X31 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('109',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_3 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v3_ordinal1 @ sk_B_3 )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('111',plain,
    ( ( v4_ordinal1 @ sk_A )
   <= ( v4_ordinal1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('112',plain,
    ( ( r2_hidden @ sk_B_3 @ sk_A )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,(
    ! [X21: $i] :
      ( ( X21
        = ( k3_tarski @ X21 ) )
      | ~ ( v4_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_ordinal1])).

thf('114',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v4_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_A )
      | ~ ( v4_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v3_ordinal1 @ X26 )
      | ~ ( v3_ordinal1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('119',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','121'])).

thf('123',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('124',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v3_ordinal1 @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('126',plain,
    ( ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B_3 ) )
   <= ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('127',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_B_3 ) @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( r1_tarski @ sk_A @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ~ ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
      & ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['100','127'])).

thf('129',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('130',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('131',plain,
    ( ~ ( r1_tarski @ sk_A @ ( sk_D_1 @ sk_B_3 @ sk_A ) )
   <= ( ( v4_ordinal1 @ sk_A )
      & ( r2_hidden @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( r2_hidden @ ( k1_ordinal1 @ sk_B_3 ) @ sk_A )
    | ~ ( v4_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','56','58','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AZzPcxMkgG
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:35:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 7.30/7.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.30/7.57  % Solved by: fo/fo7.sh
% 7.30/7.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.30/7.57  % done 6482 iterations in 7.126s
% 7.30/7.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.30/7.57  % SZS output start Refutation
% 7.30/7.57  thf(sk_B_3_type, type, sk_B_3: $i).
% 7.30/7.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.30/7.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 7.30/7.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.30/7.57  thf(sk_A_type, type, sk_A: $i).
% 7.30/7.57  thf(v4_ordinal1_type, type, v4_ordinal1: $i > $o).
% 7.30/7.57  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 7.30/7.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.30/7.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 7.30/7.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 7.30/7.57  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 7.30/7.57  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 7.30/7.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 7.30/7.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 7.30/7.57  thf(t41_ordinal1, conjecture,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( v3_ordinal1 @ A ) =>
% 7.30/7.57       ( ( v4_ordinal1 @ A ) <=>
% 7.30/7.57         ( ![B:$i]:
% 7.30/7.57           ( ( v3_ordinal1 @ B ) =>
% 7.30/7.57             ( ( r2_hidden @ B @ A ) => ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ))).
% 7.30/7.57  thf(zf_stmt_0, negated_conjecture,
% 7.30/7.57    (~( ![A:$i]:
% 7.30/7.57        ( ( v3_ordinal1 @ A ) =>
% 7.30/7.57          ( ( v4_ordinal1 @ A ) <=>
% 7.30/7.57            ( ![B:$i]:
% 7.30/7.57              ( ( v3_ordinal1 @ B ) =>
% 7.30/7.57                ( ( r2_hidden @ B @ A ) =>
% 7.30/7.57                  ( r2_hidden @ ( k1_ordinal1 @ B ) @ A ) ) ) ) ) ) )),
% 7.30/7.57    inference('cnf.neg', [status(esa)], [t41_ordinal1])).
% 7.30/7.57  thf('0', plain, (((r2_hidden @ sk_B_3 @ sk_A) | ~ (v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('1', plain, (((r2_hidden @ sk_B_3 @ sk_A)) | ~ ((v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('split', [status(esa)], ['0'])).
% 7.30/7.57  thf('2', plain,
% 7.30/7.57      (![X39 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X39)
% 7.30/7.57          | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57          | ~ (r2_hidden @ X39 @ sk_A)
% 7.30/7.57          | (v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('3', plain,
% 7.30/7.57      ((![X39 : $i]:
% 7.30/7.57          (~ (v3_ordinal1 @ X39)
% 7.30/7.57           | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57           | ~ (r2_hidden @ X39 @ sk_A))) | 
% 7.30/7.57       ((v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('split', [status(esa)], ['2'])).
% 7.30/7.57  thf(t35_ordinal1, axiom,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) =>
% 7.30/7.57       ( v3_ordinal1 @ ( k3_tarski @ A ) ) ))).
% 7.30/7.57  thf('4', plain,
% 7.30/7.57      (![X35 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ (k3_tarski @ X35))
% 7.30/7.57          | (r2_hidden @ (sk_B_1 @ X35) @ X35))),
% 7.30/7.57      inference('cnf', [status(esa)], [t35_ordinal1])).
% 7.30/7.57  thf(t23_ordinal1, axiom,
% 7.30/7.57    (![A:$i,B:$i]:
% 7.30/7.57     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 7.30/7.57  thf('5', plain,
% 7.30/7.57      (![X26 : $i, X27 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ X26)
% 7.30/7.57          | ~ (v3_ordinal1 @ X27)
% 7.30/7.57          | ~ (r2_hidden @ X26 @ X27))),
% 7.30/7.57      inference('cnf', [status(esa)], [t23_ordinal1])).
% 7.30/7.57  thf('6', plain,
% 7.30/7.57      (![X0 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ (k3_tarski @ X0))
% 7.30/7.57          | ~ (v3_ordinal1 @ X0)
% 7.30/7.57          | (v3_ordinal1 @ (sk_B_1 @ X0)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['4', '5'])).
% 7.30/7.57  thf('7', plain,
% 7.30/7.57      (![X35 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ (k3_tarski @ X35)) | ~ (v3_ordinal1 @ (sk_B_1 @ X35)))),
% 7.30/7.57      inference('cnf', [status(esa)], [t35_ordinal1])).
% 7.30/7.57  thf('8', plain,
% 7.30/7.57      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (v3_ordinal1 @ (k3_tarski @ X0)))),
% 7.30/7.57      inference('clc', [status(thm)], ['6', '7'])).
% 7.30/7.57  thf(d3_tarski, axiom,
% 7.30/7.57    (![A:$i,B:$i]:
% 7.30/7.57     ( ( r1_tarski @ A @ B ) <=>
% 7.30/7.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.30/7.57  thf('9', plain,
% 7.30/7.57      (![X1 : $i, X3 : $i]:
% 7.30/7.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.30/7.57      inference('cnf', [status(esa)], [d3_tarski])).
% 7.30/7.57  thf('10', plain,
% 7.30/7.57      (![X26 : $i, X27 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ X26)
% 7.30/7.57          | ~ (v3_ordinal1 @ X27)
% 7.30/7.57          | ~ (r2_hidden @ X26 @ X27))),
% 7.30/7.57      inference('cnf', [status(esa)], [t23_ordinal1])).
% 7.30/7.57  thf('11', plain,
% 7.30/7.57      (![X0 : $i, X1 : $i]:
% 7.30/7.57         ((r1_tarski @ X0 @ X1)
% 7.30/7.57          | ~ (v3_ordinal1 @ X0)
% 7.30/7.57          | (v3_ordinal1 @ (sk_C @ X1 @ X0)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['9', '10'])).
% 7.30/7.57  thf('12', plain,
% 7.30/7.57      (![X1 : $i, X3 : $i]:
% 7.30/7.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.30/7.57      inference('cnf', [status(esa)], [d3_tarski])).
% 7.30/7.57  thf('13', plain,
% 7.30/7.57      ((![X39 : $i]:
% 7.30/7.57          (~ (v3_ordinal1 @ X39)
% 7.30/7.57           | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57           | ~ (r2_hidden @ X39 @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('split', [status(esa)], ['2'])).
% 7.30/7.57  thf('14', plain,
% 7.30/7.57      ((![X0 : $i]:
% 7.30/7.57          ((r1_tarski @ sk_A @ X0)
% 7.30/7.57           | (r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 7.30/7.57           | ~ (v3_ordinal1 @ (sk_C @ X0 @ sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['12', '13'])).
% 7.30/7.57  thf('15', plain,
% 7.30/7.57      ((![X0 : $i]:
% 7.30/7.57          (~ (v3_ordinal1 @ sk_A)
% 7.30/7.57           | (r1_tarski @ sk_A @ X0)
% 7.30/7.57           | (r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 7.30/7.57           | (r1_tarski @ sk_A @ X0)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['11', '14'])).
% 7.30/7.57  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('17', plain,
% 7.30/7.57      ((![X0 : $i]:
% 7.30/7.57          ((r1_tarski @ sk_A @ X0)
% 7.30/7.57           | (r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 7.30/7.57           | (r1_tarski @ sk_A @ X0)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('demod', [status(thm)], ['15', '16'])).
% 7.30/7.57  thf('18', plain,
% 7.30/7.57      ((![X0 : $i]:
% 7.30/7.57          ((r2_hidden @ (k1_ordinal1 @ (sk_C @ X0 @ sk_A)) @ sk_A)
% 7.30/7.57           | (r1_tarski @ sk_A @ X0)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('simplify', [status(thm)], ['17'])).
% 7.30/7.57  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 7.30/7.57  thf('19', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_ordinal1 @ X25))),
% 7.30/7.57      inference('cnf', [status(esa)], [t10_ordinal1])).
% 7.30/7.57  thf(d4_tarski, axiom,
% 7.30/7.57    (![A:$i,B:$i]:
% 7.30/7.57     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 7.30/7.57       ( ![C:$i]:
% 7.30/7.57         ( ( r2_hidden @ C @ B ) <=>
% 7.30/7.57           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 7.30/7.57  thf('20', plain,
% 7.30/7.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X7 @ X8)
% 7.30/7.57          | ~ (r2_hidden @ X9 @ X7)
% 7.30/7.57          | (r2_hidden @ X9 @ X10)
% 7.30/7.57          | ((X10) != (k3_tarski @ X8)))),
% 7.30/7.57      inference('cnf', [status(esa)], [d4_tarski])).
% 7.30/7.57  thf('21', plain,
% 7.30/7.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.30/7.57         ((r2_hidden @ X9 @ (k3_tarski @ X8))
% 7.30/7.57          | ~ (r2_hidden @ X9 @ X7)
% 7.30/7.57          | ~ (r2_hidden @ X7 @ X8))),
% 7.30/7.57      inference('simplify', [status(thm)], ['20'])).
% 7.30/7.57  thf('22', plain,
% 7.30/7.57      (![X0 : $i, X1 : $i]:
% 7.30/7.57         (~ (r2_hidden @ (k1_ordinal1 @ X0) @ X1)
% 7.30/7.57          | (r2_hidden @ X0 @ (k3_tarski @ X1)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['19', '21'])).
% 7.30/7.57  thf('23', plain,
% 7.30/7.57      ((![X0 : $i]:
% 7.30/7.57          ((r1_tarski @ sk_A @ X0)
% 7.30/7.57           | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['18', '22'])).
% 7.30/7.57  thf('24', plain,
% 7.30/7.57      (![X1 : $i, X3 : $i]:
% 7.30/7.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.30/7.57      inference('cnf', [status(esa)], [d3_tarski])).
% 7.30/7.57  thf('25', plain,
% 7.30/7.57      ((((r1_tarski @ sk_A @ (k3_tarski @ sk_A))
% 7.30/7.57         | (r1_tarski @ sk_A @ (k3_tarski @ sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['23', '24'])).
% 7.30/7.57  thf('26', plain,
% 7.30/7.57      (((r1_tarski @ sk_A @ (k3_tarski @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('simplify', [status(thm)], ['25'])).
% 7.30/7.57  thf(t24_ordinal1, axiom,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( v3_ordinal1 @ A ) =>
% 7.30/7.57       ( ![B:$i]:
% 7.30/7.57         ( ( v3_ordinal1 @ B ) =>
% 7.30/7.57           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 7.30/7.57                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 7.30/7.57  thf('27', plain,
% 7.30/7.57      (![X28 : $i, X29 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X28)
% 7.30/7.57          | (r2_hidden @ X29 @ X28)
% 7.30/7.57          | ((X29) = (X28))
% 7.30/7.57          | (r2_hidden @ X28 @ X29)
% 7.30/7.57          | ~ (v3_ordinal1 @ X29))),
% 7.30/7.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 7.30/7.57  thf(t7_ordinal1, axiom,
% 7.30/7.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.30/7.57  thf('28', plain,
% 7.30/7.57      (![X37 : $i, X38 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 7.30/7.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.30/7.57  thf('29', plain,
% 7.30/7.57      (![X0 : $i, X1 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X1)
% 7.30/7.57          | (r2_hidden @ X0 @ X1)
% 7.30/7.57          | ((X1) = (X0))
% 7.30/7.57          | ~ (v3_ordinal1 @ X0)
% 7.30/7.57          | ~ (r1_tarski @ X0 @ X1))),
% 7.30/7.57      inference('sup-', [status(thm)], ['27', '28'])).
% 7.30/7.57  thf('30', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_A)
% 7.30/7.57         | ((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | (r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ (k3_tarski @ sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['26', '29'])).
% 7.30/7.57  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('32', plain,
% 7.30/7.57      (((((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | (r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ (k3_tarski @ sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('demod', [status(thm)], ['30', '31'])).
% 7.30/7.57  thf('33', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_A)
% 7.30/7.57         | (r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 7.30/7.57         | ((k3_tarski @ sk_A) = (sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['8', '32'])).
% 7.30/7.57  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('35', plain,
% 7.30/7.57      ((((r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 7.30/7.57         | ((k3_tarski @ sk_A) = (sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('demod', [status(thm)], ['33', '34'])).
% 7.30/7.57  thf('36', plain,
% 7.30/7.57      (![X8 : $i, X10 : $i, X11 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X11 @ X10)
% 7.30/7.57          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 7.30/7.57          | ((X10) != (k3_tarski @ X8)))),
% 7.30/7.57      inference('cnf', [status(esa)], [d4_tarski])).
% 7.30/7.57  thf('37', plain,
% 7.30/7.57      (![X8 : $i, X11 : $i]:
% 7.30/7.57         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 7.30/7.57          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 7.30/7.57      inference('simplify', [status(thm)], ['36'])).
% 7.30/7.57  thf('38', plain,
% 7.30/7.57      (((((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['35', '37'])).
% 7.30/7.57  thf(d2_ordinal1, axiom,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( v1_ordinal1 @ A ) <=>
% 7.30/7.57       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 7.30/7.57  thf('39', plain,
% 7.30/7.57      (![X18 : $i, X19 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X18 @ X19)
% 7.30/7.57          | (r1_tarski @ X18 @ X19)
% 7.30/7.57          | ~ (v1_ordinal1 @ X19))),
% 7.30/7.57      inference('cnf', [status(esa)], [d2_ordinal1])).
% 7.30/7.57  thf('40', plain,
% 7.30/7.57      (((((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | ~ (v1_ordinal1 @ sk_A)
% 7.30/7.57         | (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['38', '39'])).
% 7.30/7.57  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf(cc1_ordinal1, axiom,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 7.30/7.57  thf('42', plain,
% 7.30/7.57      (![X14 : $i]: ((v1_ordinal1 @ X14) | ~ (v3_ordinal1 @ X14))),
% 7.30/7.57      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 7.30/7.57  thf('43', plain, ((v1_ordinal1 @ sk_A)),
% 7.30/7.57      inference('sup-', [status(thm)], ['41', '42'])).
% 7.30/7.57  thf('44', plain,
% 7.30/7.57      (((((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('demod', [status(thm)], ['40', '43'])).
% 7.30/7.57  thf('45', plain,
% 7.30/7.57      ((((r2_hidden @ sk_A @ (k3_tarski @ sk_A))
% 7.30/7.57         | ((k3_tarski @ sk_A) = (sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('demod', [status(thm)], ['33', '34'])).
% 7.30/7.57  thf('46', plain,
% 7.30/7.57      (![X8 : $i, X10 : $i, X11 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X11 @ X10)
% 7.30/7.57          | (r2_hidden @ X11 @ (sk_D_1 @ X11 @ X8))
% 7.30/7.57          | ((X10) != (k3_tarski @ X8)))),
% 7.30/7.57      inference('cnf', [status(esa)], [d4_tarski])).
% 7.30/7.57  thf('47', plain,
% 7.30/7.57      (![X8 : $i, X11 : $i]:
% 7.30/7.57         ((r2_hidden @ X11 @ (sk_D_1 @ X11 @ X8))
% 7.30/7.57          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 7.30/7.57      inference('simplify', [status(thm)], ['46'])).
% 7.30/7.57  thf('48', plain,
% 7.30/7.57      (((((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | (r2_hidden @ sk_A @ (sk_D_1 @ sk_A @ sk_A))))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['45', '47'])).
% 7.30/7.57  thf('49', plain,
% 7.30/7.57      (![X37 : $i, X38 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 7.30/7.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.30/7.57  thf('50', plain,
% 7.30/7.57      (((((k3_tarski @ sk_A) = (sk_A))
% 7.30/7.57         | ~ (r1_tarski @ (sk_D_1 @ sk_A @ sk_A) @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['48', '49'])).
% 7.30/7.57  thf('51', plain,
% 7.30/7.57      ((((k3_tarski @ sk_A) = (sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('clc', [status(thm)], ['44', '50'])).
% 7.30/7.57  thf(d6_ordinal1, axiom,
% 7.30/7.57    (![A:$i]: ( ( v4_ordinal1 @ A ) <=> ( ( A ) = ( k3_tarski @ A ) ) ))).
% 7.30/7.57  thf('52', plain,
% 7.30/7.57      (![X22 : $i]: ((v4_ordinal1 @ X22) | ((X22) != (k3_tarski @ X22)))),
% 7.30/7.57      inference('cnf', [status(esa)], [d6_ordinal1])).
% 7.30/7.57  thf('53', plain,
% 7.30/7.57      (((((sk_A) != (sk_A)) | (v4_ordinal1 @ sk_A)))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('sup-', [status(thm)], ['51', '52'])).
% 7.30/7.57  thf('54', plain,
% 7.30/7.57      (((v4_ordinal1 @ sk_A))
% 7.30/7.57         <= ((![X39 : $i]:
% 7.30/7.57                (~ (v3_ordinal1 @ X39)
% 7.30/7.57                 | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57                 | ~ (r2_hidden @ X39 @ sk_A))))),
% 7.30/7.57      inference('simplify', [status(thm)], ['53'])).
% 7.30/7.57  thf('55', plain, ((~ (v4_ordinal1 @ sk_A)) <= (~ ((v4_ordinal1 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['0'])).
% 7.30/7.57  thf('56', plain,
% 7.30/7.57      (~
% 7.30/7.57       (![X39 : $i]:
% 7.30/7.57          (~ (v3_ordinal1 @ X39)
% 7.30/7.57           | (r2_hidden @ (k1_ordinal1 @ X39) @ sk_A)
% 7.30/7.57           | ~ (r2_hidden @ X39 @ sk_A))) | 
% 7.30/7.57       ((v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('sup-', [status(thm)], ['54', '55'])).
% 7.30/7.57  thf('57', plain,
% 7.30/7.57      ((~ (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A) | ~ (v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('58', plain,
% 7.30/7.57      (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) | 
% 7.30/7.57       ~ ((v4_ordinal1 @ sk_A))),
% 7.30/7.57      inference('split', [status(esa)], ['57'])).
% 7.30/7.57  thf(t29_ordinal1, axiom,
% 7.30/7.57    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 7.30/7.57  thf('59', plain,
% 7.30/7.57      (![X30 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ (k1_ordinal1 @ X30)) | ~ (v3_ordinal1 @ X30))),
% 7.30/7.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 7.30/7.57  thf('60', plain,
% 7.30/7.57      (![X30 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ (k1_ordinal1 @ X30)) | ~ (v3_ordinal1 @ X30))),
% 7.30/7.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 7.30/7.57  thf('61', plain,
% 7.30/7.57      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['0'])).
% 7.30/7.57  thf(t33_ordinal1, axiom,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( v3_ordinal1 @ A ) =>
% 7.30/7.57       ( ![B:$i]:
% 7.30/7.57         ( ( v3_ordinal1 @ B ) =>
% 7.30/7.57           ( ( r2_hidden @ A @ B ) <=>
% 7.30/7.57             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 7.30/7.57  thf('62', plain,
% 7.30/7.57      (![X31 : $i, X32 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X31)
% 7.30/7.57          | ~ (r2_hidden @ X32 @ X31)
% 7.30/7.57          | (r1_ordinal1 @ (k1_ordinal1 @ X32) @ X31)
% 7.30/7.57          | ~ (v3_ordinal1 @ X32))),
% 7.30/7.57      inference('cnf', [status(esa)], [t33_ordinal1])).
% 7.30/7.57  thf('63', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_B_3)
% 7.30/7.57         | (r1_ordinal1 @ (k1_ordinal1 @ sk_B_3) @ sk_A)
% 7.30/7.57         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['61', '62'])).
% 7.30/7.57  thf('64', plain,
% 7.30/7.57      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['0'])).
% 7.30/7.57  thf('65', plain,
% 7.30/7.57      (![X26 : $i, X27 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ X26)
% 7.30/7.57          | ~ (v3_ordinal1 @ X27)
% 7.30/7.57          | ~ (r2_hidden @ X26 @ X27))),
% 7.30/7.57      inference('cnf', [status(esa)], [t23_ordinal1])).
% 7.30/7.57  thf('66', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ sk_B_3)))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['64', '65'])).
% 7.30/7.57  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('68', plain,
% 7.30/7.57      (((v3_ordinal1 @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['66', '67'])).
% 7.30/7.57  thf('69', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('70', plain,
% 7.30/7.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_B_3) @ sk_A))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['63', '68', '69'])).
% 7.30/7.57  thf(t34_ordinal1, axiom,
% 7.30/7.57    (![A:$i]:
% 7.30/7.57     ( ( v3_ordinal1 @ A ) =>
% 7.30/7.57       ( ![B:$i]:
% 7.30/7.57         ( ( v3_ordinal1 @ B ) =>
% 7.30/7.57           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 7.30/7.57             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 7.30/7.57  thf('71', plain,
% 7.30/7.57      (![X33 : $i, X34 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X33)
% 7.30/7.57          | ~ (r1_ordinal1 @ X34 @ X33)
% 7.30/7.57          | (r2_hidden @ X34 @ (k1_ordinal1 @ X33))
% 7.30/7.57          | ~ (v3_ordinal1 @ X34))),
% 7.30/7.57      inference('cnf', [status(esa)], [t34_ordinal1])).
% 7.30/7.57  thf('72', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))
% 7.30/7.57         | (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ (k1_ordinal1 @ sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['70', '71'])).
% 7.30/7.57  thf('73', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('74', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))
% 7.30/7.57         | (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ (k1_ordinal1 @ sk_A))))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['72', '73'])).
% 7.30/7.57  thf('75', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_B_3)
% 7.30/7.57         | (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ (k1_ordinal1 @ sk_A))))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['60', '74'])).
% 7.30/7.57  thf('76', plain,
% 7.30/7.57      (((v3_ordinal1 @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['66', '67'])).
% 7.30/7.57  thf('77', plain,
% 7.30/7.57      (((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ (k1_ordinal1 @ sk_A)))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['75', '76'])).
% 7.30/7.57  thf('78', plain,
% 7.30/7.57      (![X26 : $i, X27 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ X26)
% 7.30/7.57          | ~ (v3_ordinal1 @ X27)
% 7.30/7.57          | ~ (r2_hidden @ X26 @ X27))),
% 7.30/7.57      inference('cnf', [status(esa)], [t23_ordinal1])).
% 7.30/7.57  thf('79', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 7.30/7.57         | (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['77', '78'])).
% 7.30/7.57  thf('80', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['59', '79'])).
% 7.30/7.57  thf('81', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('82', plain,
% 7.30/7.57      (((v3_ordinal1 @ (k1_ordinal1 @ sk_B_3)))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['80', '81'])).
% 7.30/7.57  thf('83', plain,
% 7.30/7.57      (![X28 : $i, X29 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X28)
% 7.30/7.57          | (r2_hidden @ X29 @ X28)
% 7.30/7.57          | ((X29) = (X28))
% 7.30/7.57          | (r2_hidden @ X28 @ X29)
% 7.30/7.57          | ~ (v3_ordinal1 @ X29))),
% 7.30/7.57      inference('cnf', [status(esa)], [t24_ordinal1])).
% 7.30/7.57  thf('84', plain,
% 7.30/7.57      ((~ (r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['57'])).
% 7.30/7.57  thf('85', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))
% 7.30/7.57         | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))
% 7.30/7.57         | ((k1_ordinal1 @ sk_B_3) = (sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ sk_A)))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['83', '84'])).
% 7.30/7.57  thf('86', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('87', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))
% 7.30/7.57         | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))
% 7.30/7.57         | ((k1_ordinal1 @ sk_B_3) = (sk_A))))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['85', '86'])).
% 7.30/7.57  thf('88', plain,
% 7.30/7.57      (((((k1_ordinal1 @ sk_B_3) = (sk_A))
% 7.30/7.57         | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_3))))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 7.30/7.57             ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['82', '87'])).
% 7.30/7.57  thf('89', plain,
% 7.30/7.57      (![X37 : $i, X38 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 7.30/7.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.30/7.57  thf('90', plain,
% 7.30/7.57      (((((k1_ordinal1 @ sk_B_3) = (sk_A))
% 7.30/7.57         | ~ (r1_tarski @ (k1_ordinal1 @ sk_B_3) @ sk_A)))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 7.30/7.57             ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['88', '89'])).
% 7.30/7.57  thf('91', plain,
% 7.30/7.57      (![X30 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ (k1_ordinal1 @ X30)) | ~ (v3_ordinal1 @ X30))),
% 7.30/7.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 7.30/7.57  thf('92', plain,
% 7.30/7.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_B_3) @ sk_A))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['63', '68', '69'])).
% 7.30/7.57  thf(redefinition_r1_ordinal1, axiom,
% 7.30/7.57    (![A:$i,B:$i]:
% 7.30/7.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 7.30/7.57       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 7.30/7.57  thf('93', plain,
% 7.30/7.57      (![X23 : $i, X24 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X23)
% 7.30/7.57          | ~ (v3_ordinal1 @ X24)
% 7.30/7.57          | (r1_tarski @ X23 @ X24)
% 7.30/7.57          | ~ (r1_ordinal1 @ X23 @ X24))),
% 7.30/7.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 7.30/7.57  thf('94', plain,
% 7.30/7.57      ((((r1_tarski @ (k1_ordinal1 @ sk_B_3) @ sk_A)
% 7.30/7.57         | ~ (v3_ordinal1 @ sk_A)
% 7.30/7.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['92', '93'])).
% 7.30/7.57  thf('95', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('96', plain,
% 7.30/7.57      ((((r1_tarski @ (k1_ordinal1 @ sk_B_3) @ sk_A)
% 7.30/7.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['94', '95'])).
% 7.30/7.57  thf('97', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_B_3) | (r1_tarski @ (k1_ordinal1 @ sk_B_3) @ sk_A)))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['91', '96'])).
% 7.30/7.57  thf('98', plain,
% 7.30/7.57      (((v3_ordinal1 @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['66', '67'])).
% 7.30/7.57  thf('99', plain,
% 7.30/7.57      (((r1_tarski @ (k1_ordinal1 @ sk_B_3) @ sk_A))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['97', '98'])).
% 7.30/7.57  thf('100', plain,
% 7.30/7.57      ((((k1_ordinal1 @ sk_B_3) = (sk_A)))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 7.30/7.57             ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['90', '99'])).
% 7.30/7.57  thf('101', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['2'])).
% 7.30/7.57  thf('102', plain,
% 7.30/7.57      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['0'])).
% 7.30/7.57  thf('103', plain,
% 7.30/7.57      (![X21 : $i]: (((X21) = (k3_tarski @ X21)) | ~ (v4_ordinal1 @ X21))),
% 7.30/7.57      inference('cnf', [status(esa)], [d6_ordinal1])).
% 7.30/7.57  thf('104', plain,
% 7.30/7.57      (![X8 : $i, X11 : $i]:
% 7.30/7.57         ((r2_hidden @ X11 @ (sk_D_1 @ X11 @ X8))
% 7.30/7.57          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 7.30/7.57      inference('simplify', [status(thm)], ['46'])).
% 7.30/7.57  thf('105', plain,
% 7.30/7.57      (![X0 : $i, X1 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X1 @ X0)
% 7.30/7.57          | ~ (v4_ordinal1 @ X0)
% 7.30/7.57          | (r2_hidden @ X1 @ (sk_D_1 @ X1 @ X0)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['103', '104'])).
% 7.30/7.57  thf('106', plain,
% 7.30/7.57      ((((r2_hidden @ sk_B_3 @ (sk_D_1 @ sk_B_3 @ sk_A))
% 7.30/7.57         | ~ (v4_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['102', '105'])).
% 7.30/7.57  thf('107', plain,
% 7.30/7.57      (((r2_hidden @ sk_B_3 @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['101', '106'])).
% 7.30/7.57  thf('108', plain,
% 7.30/7.57      (![X31 : $i, X32 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X31)
% 7.30/7.57          | ~ (r2_hidden @ X32 @ X31)
% 7.30/7.57          | (r1_ordinal1 @ (k1_ordinal1 @ X32) @ X31)
% 7.30/7.57          | ~ (v3_ordinal1 @ X32))),
% 7.30/7.57      inference('cnf', [status(esa)], [t33_ordinal1])).
% 7.30/7.57  thf('109', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_B_3)
% 7.30/7.57         | (r1_ordinal1 @ (k1_ordinal1 @ sk_B_3) @ (sk_D_1 @ sk_B_3 @ sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A))))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['107', '108'])).
% 7.30/7.57  thf('110', plain,
% 7.30/7.57      (((v3_ordinal1 @ sk_B_3)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['66', '67'])).
% 7.30/7.57  thf('111', plain, (((v4_ordinal1 @ sk_A)) <= (((v4_ordinal1 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['2'])).
% 7.30/7.57  thf('112', plain,
% 7.30/7.57      (((r2_hidden @ sk_B_3 @ sk_A)) <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('split', [status(esa)], ['0'])).
% 7.30/7.57  thf('113', plain,
% 7.30/7.57      (![X21 : $i]: (((X21) = (k3_tarski @ X21)) | ~ (v4_ordinal1 @ X21))),
% 7.30/7.57      inference('cnf', [status(esa)], [d6_ordinal1])).
% 7.30/7.57  thf('114', plain,
% 7.30/7.57      (![X8 : $i, X11 : $i]:
% 7.30/7.57         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 7.30/7.57          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 7.30/7.57      inference('simplify', [status(thm)], ['36'])).
% 7.30/7.57  thf('115', plain,
% 7.30/7.57      (![X0 : $i, X1 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X1 @ X0)
% 7.30/7.57          | ~ (v4_ordinal1 @ X0)
% 7.30/7.57          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ X0))),
% 7.30/7.57      inference('sup-', [status(thm)], ['113', '114'])).
% 7.30/7.57  thf('116', plain,
% 7.30/7.57      ((((r2_hidden @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_A) | ~ (v4_ordinal1 @ sk_A)))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['112', '115'])).
% 7.30/7.57  thf('117', plain,
% 7.30/7.57      (((r2_hidden @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_A))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['111', '116'])).
% 7.30/7.57  thf('118', plain,
% 7.30/7.57      (![X26 : $i, X27 : $i]:
% 7.30/7.57         ((v3_ordinal1 @ X26)
% 7.30/7.57          | ~ (v3_ordinal1 @ X27)
% 7.30/7.57          | ~ (r2_hidden @ X26 @ X27))),
% 7.30/7.57      inference('cnf', [status(esa)], [t23_ordinal1])).
% 7.30/7.57  thf('119', plain,
% 7.30/7.57      (((~ (v3_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A))))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['117', '118'])).
% 7.30/7.57  thf('120', plain, ((v3_ordinal1 @ sk_A)),
% 7.30/7.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.30/7.57  thf('121', plain,
% 7.30/7.57      (((v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['119', '120'])).
% 7.30/7.57  thf('122', plain,
% 7.30/7.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_B_3) @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['109', '110', '121'])).
% 7.30/7.57  thf('123', plain,
% 7.30/7.57      (![X23 : $i, X24 : $i]:
% 7.30/7.57         (~ (v3_ordinal1 @ X23)
% 7.30/7.57          | ~ (v3_ordinal1 @ X24)
% 7.30/7.57          | (r1_tarski @ X23 @ X24)
% 7.30/7.57          | ~ (r1_ordinal1 @ X23 @ X24))),
% 7.30/7.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 7.30/7.57  thf('124', plain,
% 7.30/7.57      ((((r1_tarski @ (k1_ordinal1 @ sk_B_3) @ (sk_D_1 @ sk_B_3 @ sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A))
% 7.30/7.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B_3))))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['122', '123'])).
% 7.30/7.57  thf('125', plain,
% 7.30/7.57      (((v3_ordinal1 @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['119', '120'])).
% 7.30/7.57  thf('126', plain,
% 7.30/7.57      (((v3_ordinal1 @ (k1_ordinal1 @ sk_B_3)))
% 7.30/7.57         <= (((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['80', '81'])).
% 7.30/7.57  thf('127', plain,
% 7.30/7.57      (((r1_tarski @ (k1_ordinal1 @ sk_B_3) @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('demod', [status(thm)], ['124', '125', '126'])).
% 7.30/7.57  thf('128', plain,
% 7.30/7.57      (((r1_tarski @ sk_A @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (~ ((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) & 
% 7.30/7.57             ((v4_ordinal1 @ sk_A)) & 
% 7.30/7.57             ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup+', [status(thm)], ['100', '127'])).
% 7.30/7.57  thf('129', plain,
% 7.30/7.57      (((r2_hidden @ (sk_D_1 @ sk_B_3 @ sk_A) @ sk_A))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['111', '116'])).
% 7.30/7.57  thf('130', plain,
% 7.30/7.57      (![X37 : $i, X38 : $i]:
% 7.30/7.57         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 7.30/7.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.30/7.57  thf('131', plain,
% 7.30/7.57      ((~ (r1_tarski @ sk_A @ (sk_D_1 @ sk_B_3 @ sk_A)))
% 7.30/7.57         <= (((v4_ordinal1 @ sk_A)) & ((r2_hidden @ sk_B_3 @ sk_A)))),
% 7.30/7.57      inference('sup-', [status(thm)], ['129', '130'])).
% 7.30/7.57  thf('132', plain,
% 7.30/7.57      (((r2_hidden @ (k1_ordinal1 @ sk_B_3) @ sk_A)) | 
% 7.30/7.57       ~ ((v4_ordinal1 @ sk_A)) | ~ ((r2_hidden @ sk_B_3 @ sk_A))),
% 7.30/7.57      inference('sup-', [status(thm)], ['128', '131'])).
% 7.30/7.57  thf('133', plain, ($false),
% 7.30/7.57      inference('sat_resolution*', [status(thm)], ['1', '3', '56', '58', '132'])).
% 7.30/7.57  
% 7.30/7.57  % SZS output end Refutation
% 7.30/7.57  
% 7.30/7.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
