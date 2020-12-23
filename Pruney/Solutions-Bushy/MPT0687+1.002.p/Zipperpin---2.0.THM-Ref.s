%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0687+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N6gkJXYmeN

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:19 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 143 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  602 (1272 expanded)
%              Number of equality atoms :   36 (  87 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_E_1 @ X5 @ X1 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_E_1 @ ( sk_B @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i,X5: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_E_1 @ X5 @ X1 @ X2 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('18',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('27',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k10_relat_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k10_relat_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
      & ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('39',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('40',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('41',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['21','43','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['19','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('51',plain,(
    ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['21','43'])).

thf('52',plain,(
    ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','52'])).


%------------------------------------------------------------------------------
