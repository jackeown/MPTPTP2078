%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2F4BzlCmBL

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:42 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 121 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  804 (1086 expanded)
%              Number of equality atoms :   39 (  58 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X37: $i] :
      ( ( ( k10_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X43
       != ( k10_relat_1 @ X42 @ X41 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X44 ) @ X41 )
      | ~ ( r2_hidden @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('8',plain,(
    ! [X41: $i,X42: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( r2_hidden @ X44 @ ( k10_relat_1 @ X42 @ X41 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X44 ) @ X41 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X47: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('14',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X41: $i,X42: $i,X43: $i,X45: $i] :
      ( ( X43
       != ( k10_relat_1 @ X42 @ X41 ) )
      | ( r2_hidden @ X45 @ X43 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X42 @ X45 ) @ X41 )
      | ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('20',plain,(
    ! [X41: $i,X42: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ X42 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X42 @ X45 ) @ X41 )
      | ( r2_hidden @ X45 @ ( k10_relat_1 @ X42 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X47: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) )
    | ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X43
       != ( k10_relat_1 @ X42 @ X41 ) )
      | ( r2_hidden @ X44 @ ( k1_relat_1 @ X42 ) )
      | ~ ( r2_hidden @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('34',plain,(
    ! [X41: $i,X42: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( r2_hidden @ X44 @ ( k10_relat_1 @ X42 @ X41 ) )
      | ( r2_hidden @ X44 @ ( k1_relat_1 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X47: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','44'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X36: $i] :
      ( ( ( k9_relat_1 @ X36 @ ( k1_relat_1 @ X36 ) )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k9_relat_1 @ X52 @ ( k10_relat_1 @ X52 @ X51 ) )
        = ( k3_xboole_0 @ X51 @ ( k9_relat_1 @ X52 @ ( k1_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X36: $i] :
      ( ( ( k9_relat_1 @ X36 @ ( k1_relat_1 @ X36 ) )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X47: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','56','57','58','59'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('61',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X49 @ X48 ) @ X50 )
        = ( k3_xboole_0 @ X48 @ ( k10_relat_1 @ X49 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('62',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2F4BzlCmBL
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 104 iterations in 0.102s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(d3_tarski, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      (![X1 : $i, X3 : $i]:
% 0.35/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf(t71_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.35/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.55  thf('1', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf(t169_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X37 : $i]:
% 0.35/0.55         (((k10_relat_1 @ X37 @ (k2_relat_1 @ X37)) = (k1_relat_1 @ X37))
% 0.35/0.55          | ~ (v1_relat_1 @ X37))),
% 0.35/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.35/0.55            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.35/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.35/0.55  thf('4', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf(fc3_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.35/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.35/0.55  thf('5', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.35/0.55  thf(d13_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ![B:$i,C:$i]:
% 0.35/0.55         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.35/0.55           ( ![D:$i]:
% 0.35/0.55             ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.55               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.35/0.55                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.35/0.55         (((X43) != (k10_relat_1 @ X42 @ X41))
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ X42 @ X44) @ X41)
% 0.35/0.55          | ~ (r2_hidden @ X44 @ X43)
% 0.35/0.55          | ~ (v1_funct_1 @ X42)
% 0.35/0.55          | ~ (v1_relat_1 @ X42))),
% 0.35/0.55      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i, X44 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X42)
% 0.35/0.55          | ~ (v1_funct_1 @ X42)
% 0.35/0.55          | ~ (r2_hidden @ X44 @ (k10_relat_1 @ X42 @ X41))
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ X42 @ X44) @ X41))),
% 0.35/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.35/0.55  thf('10', plain, (![X47 : $i]: (v1_funct_1 @ (k6_relat_1 @ X47))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('11', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r1_tarski @ X0 @ X1)
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ (sk_C @ X1 @ X0)) @ 
% 0.35/0.55             X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['0', '12'])).
% 0.35/0.55  thf(t175_funct_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ![B:$i,C:$i]:
% 0.35/0.55         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.35/0.55           ( ( k10_relat_1 @ A @ C ) =
% 0.35/0.55             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55          ( ![B:$i,C:$i]:
% 0.35/0.55            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.35/0.55              ( ( k10_relat_1 @ A @ C ) =
% 0.35/0.55                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.35/0.55  thf('14', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.55          | (r2_hidden @ X0 @ X2)
% 0.35/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r2_hidden @ X0 @ sk_B)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ X0)
% 0.35/0.55          | (r2_hidden @ 
% 0.35/0.55             (k1_funct_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.35/0.55              (sk_C @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1))) @ 
% 0.35/0.55             sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.35/0.55  thf('18', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i, X43 : $i, X45 : $i]:
% 0.35/0.55         (((X43) != (k10_relat_1 @ X42 @ X41))
% 0.35/0.55          | (r2_hidden @ X45 @ X43)
% 0.35/0.55          | ~ (r2_hidden @ (k1_funct_1 @ X42 @ X45) @ X41)
% 0.35/0.55          | ~ (r2_hidden @ X45 @ (k1_relat_1 @ X42))
% 0.35/0.55          | ~ (v1_funct_1 @ X42)
% 0.35/0.55          | ~ (v1_relat_1 @ X42))),
% 0.35/0.55      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i, X45 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X42)
% 0.35/0.55          | ~ (v1_funct_1 @ X42)
% 0.35/0.55          | ~ (r2_hidden @ X45 @ (k1_relat_1 @ X42))
% 0.35/0.55          | ~ (r2_hidden @ (k1_funct_1 @ X42 @ X45) @ X41)
% 0.35/0.55          | (r2_hidden @ X45 @ (k10_relat_1 @ X42 @ X41)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.35/0.55          | ~ (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 0.35/0.55          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.35/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.35/0.55  thf('22', plain, (![X47 : $i]: (v1_funct_1 @ (k6_relat_1 @ X47))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('23', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.35/0.55          | ~ (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1) @ X2))),
% 0.35/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ X0)
% 0.35/0.55          | (r2_hidden @ (sk_C @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.35/0.55             (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))
% 0.35/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.35/0.55               (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X1 : $i, X3 : $i]:
% 0.35/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r2_hidden @ (sk_C @ X0 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.35/0.55           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))
% 0.35/0.55          | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 0.35/0.55      inference('clc', [status(thm)], ['25', '26'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (![X1 : $i, X3 : $i]:
% 0.35/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.35/0.55         (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))
% 0.35/0.55        | (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.35/0.55           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.35/0.55        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.35/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.55  thf('31', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X1 : $i, X3 : $i]:
% 0.35/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.35/0.55         (((X43) != (k10_relat_1 @ X42 @ X41))
% 0.35/0.55          | (r2_hidden @ X44 @ (k1_relat_1 @ X42))
% 0.35/0.55          | ~ (r2_hidden @ X44 @ X43)
% 0.35/0.55          | ~ (v1_funct_1 @ X42)
% 0.35/0.55          | ~ (v1_relat_1 @ X42))),
% 0.35/0.55      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i, X44 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X42)
% 0.35/0.55          | ~ (v1_funct_1 @ X42)
% 0.35/0.55          | ~ (r2_hidden @ X44 @ (k10_relat_1 @ X42 @ X41))
% 0.35/0.55          | (r2_hidden @ X44 @ (k1_relat_1 @ X42)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.35/0.55          | (r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.35/0.55             (k1_relat_1 @ X1))
% 0.35/0.55          | ~ (v1_funct_1 @ X1)
% 0.35/0.55          | ~ (v1_relat_1 @ X1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['32', '34'])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      (![X1 : $i, X3 : $i]:
% 0.35/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X0)
% 0.35/0.55          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.35/0.55          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.35/0.55          | ~ (v1_funct_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0))),
% 0.35/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.35/0.55          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['31', '38'])).
% 0.35/0.55  thf('40', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('41', plain, (![X47 : $i]: (v1_funct_1 @ (k6_relat_1 @ X47))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.35/0.55      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.35/0.55  thf(d10_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      (![X4 : $i, X6 : $i]:
% 0.35/0.55         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.35/0.55          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.35/0.55         = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['30', '44'])).
% 0.35/0.55  thf(t146_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      (![X36 : $i]:
% 0.35/0.55         (((k9_relat_1 @ X36 @ (k1_relat_1 @ X36)) = (k2_relat_1 @ X36))
% 0.35/0.55          | ~ (v1_relat_1 @ X36))),
% 0.35/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.35/0.55  thf(t148_funct_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.55       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.35/0.55         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      (![X51 : $i, X52 : $i]:
% 0.35/0.55         (((k9_relat_1 @ X52 @ (k10_relat_1 @ X52 @ X51))
% 0.35/0.55            = (k3_xboole_0 @ X51 @ (k9_relat_1 @ X52 @ (k1_relat_1 @ X52))))
% 0.35/0.55          | ~ (v1_funct_1 @ X52)
% 0.35/0.55          | ~ (v1_relat_1 @ X52))),
% 0.35/0.55      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.35/0.55            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (v1_funct_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.35/0.55              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.35/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      ((((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.35/0.55          (k10_relat_1 @ sk_A @ sk_C_1))
% 0.35/0.55          = (k3_xboole_0 @ sk_B @ 
% 0.35/0.55             (k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))))
% 0.35/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.35/0.55        | ~ (v1_funct_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_1))))),
% 0.35/0.55      inference('sup+', [status(thm)], ['45', '49'])).
% 0.35/0.55  thf('51', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      (![X36 : $i]:
% 0.35/0.55         (((k9_relat_1 @ X36 @ (k1_relat_1 @ X36)) = (k2_relat_1 @ X36))
% 0.35/0.55          | ~ (v1_relat_1 @ X36))),
% 0.35/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.35/0.55  thf('53', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.35/0.55            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.35/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.35/0.55  thf('54', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf('55', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.35/0.55  thf('57', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.35/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.55  thf('58', plain, (![X46 : $i]: (v1_relat_1 @ (k6_relat_1 @ X46))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('59', plain, (![X47 : $i]: (v1_funct_1 @ (k6_relat_1 @ X47))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.35/0.55  thf('60', plain,
% 0.35/0.55      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.35/0.55         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['50', '56', '57', '58', '59'])).
% 0.35/0.55  thf(t139_funct_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ C ) =>
% 0.35/0.55       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.35/0.55         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.35/0.55         (((k10_relat_1 @ (k7_relat_1 @ X49 @ X48) @ X50)
% 0.35/0.55            = (k3_xboole_0 @ X48 @ (k10_relat_1 @ X49 @ X50)))
% 0.35/0.55          | ~ (v1_relat_1 @ X49))),
% 0.35/0.55      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.35/0.55  thf('62', plain,
% 0.35/0.55      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.35/0.55         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('63', plain,
% 0.35/0.55      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.35/0.55          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.55  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('65', plain,
% 0.35/0.55      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.35/0.55         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.35/0.55  thf('66', plain, ($false),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['60', '65'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
