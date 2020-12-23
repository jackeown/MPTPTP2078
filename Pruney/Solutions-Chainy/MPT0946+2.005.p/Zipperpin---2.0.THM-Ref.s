%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlhmIuNDxI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  192 (1823 expanded)
%              Number of leaves         :   28 ( 553 expanded)
%              Depth                    :   50
%              Number of atoms          : 1500 (17527 expanded)
%              Number of equality atoms :   72 (1011 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X9 @ X11 ) @ X10 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X9 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k2_wellord1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('17',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
      = ( k2_wellord1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_wellord2 @ X0 )
        = ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k1_wellord2 @ X0 )
        = ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('23',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_B )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('44',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
      = ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

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

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('53',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('55',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51','55'])).

thf('57',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('58',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','66'])).

thf('68',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('75',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('80',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('82',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('83',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','83'])).

thf('85',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r4_wellord1 @ X12 @ X13 )
      | ~ ( r4_wellord1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('90',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('91',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf('92',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r4_wellord1 @ X15 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ X16 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('95',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','96'])).

thf('98',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('99',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['84','99','100','101'])).

thf('103',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('105',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','105'])).

thf('107',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_ordinal1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('110',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('115',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
      = ( k2_wellord1 @ ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('117',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('119',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51','55'])).

thf('121',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('123',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r4_wellord1 @ X15 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ X16 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('127',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('131',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['121','131','132','133'])).

thf('135',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','136'])).

thf('138',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','139'])).

thf('141',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('148',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('153',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('155',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('156',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('157',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('158',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('159',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158'])).

thf('160',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','159'])).

thf('161',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['160','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlhmIuNDxI
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:56:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 221 iterations in 0.085s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.50  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.50  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.50  thf(t7_wellord2, axiom,
% 0.20/0.50    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.50  thf(t24_ordinal1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.50           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.50                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X7)
% 0.20/0.50          | (r2_hidden @ X8 @ X7)
% 0.20/0.50          | ((X8) = (X7))
% 0.20/0.50          | (r2_hidden @ X7 @ X8)
% 0.20/0.50          | ~ (v3_ordinal1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.50  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.50       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X3)
% 0.20/0.50          | ~ (v3_ordinal1 @ X4)
% 0.20/0.50          | (r1_ordinal1 @ X3 @ X4)
% 0.20/0.50          | (r1_ordinal1 @ X4 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.50  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.50       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (v3_ordinal1 @ X5)
% 0.20/0.50          | ~ (v3_ordinal1 @ X6)
% 0.20/0.50          | (r1_tarski @ X5 @ X6)
% 0.20/0.50          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1)
% 0.20/0.50          | (r1_tarski @ X1 @ X0)
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X0)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.50  thf(t8_wellord2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.50       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.20/0.50          | ~ (r1_tarski @ X27 @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.50          | ~ (v3_ordinal1 @ X1)
% 0.20/0.50          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.50          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.20/0.51          | ~ (r1_tarski @ X27 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf(t27_wellord1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.51         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k2_wellord1 @ X9 @ X11) @ X10)
% 0.20/0.51            = (k2_wellord1 @ (k2_wellord1 @ X9 @ X10) @ X11))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.51            = (k2_wellord1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.51  thf('17', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.51           = (k2_wellord1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k1_wellord2 @ X1) @ X0)
% 0.20/0.51            = (k2_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['10', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_wellord2 @ X0) = (k2_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ((k1_wellord2 @ X0) = (k2_wellord1 @ (k1_wellord2 @ X0) @ X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r2_hidden @ X8 @ X7)
% 0.20/0.51          | ((X8) = (X7))
% 0.20/0.51          | (r2_hidden @ X7 @ X8)
% 0.20/0.51          | ~ (v3_ordinal1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.51  thf(t11_wellord2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.51             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.20/0.51                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.20/0.51  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ sk_B)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_tarski @ sk_B @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.51          | ((X0) = (sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.51  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.51  thf('36', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X5)
% 0.20/0.51          | ~ (v3_ordinal1 @ X6)
% 0.20/0.51          | (r1_tarski @ X5 @ X6)
% 0.20/0.51          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | (r1_tarski @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r1_tarski @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.20/0.51          | ~ (r1_tarski @ X27 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r2_hidden @ X8 @ X7)
% 0.20/0.51          | ((X8) = (X7))
% 0.20/0.51          | (r2_hidden @ X7 @ X8)
% 0.20/0.51          | ~ (v3_ordinal1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.51  thf(t10_wellord2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r2_hidden @ A @ B ) =>
% 0.20/0.51             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X24)
% 0.20/0.51          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.20/0.51          | ~ (r2_hidden @ X25 @ X24)
% 0.20/0.51          | ~ (v3_ordinal1 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ((X1) = (X0))
% 0.20/0.51          | (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf(t57_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( v2_wellord1 @ A ) =>
% 0.20/0.51         ( ![B:$i]:
% 0.20/0.51           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.51                ( r4_wellord1 @
% 0.20/0.51                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X17)
% 0.20/0.51          | ~ (r4_wellord1 @ X17 @ 
% 0.20/0.51               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ X1 @ X0)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf(d1_wellord2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.51         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.51           ( ![C:$i,D:$i]:
% 0.20/0.51             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.51                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         (((X20) != (k1_wellord2 @ X19))
% 0.20/0.51          | ((k3_relat_1 @ X20) = (X19))
% 0.20/0.51          | ~ (v1_relat_1 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X19 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.20/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.51  thf('54', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('55', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ X1 @ X0)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('60', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.20/0.51  thf('62', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '63'])).
% 0.20/0.51  thf('65', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '66'])).
% 0.20/0.51  thf('68', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('69', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.51  thf('72', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X24)
% 0.20/0.51          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.20/0.51          | ~ (r2_hidden @ X25 @ X24)
% 0.20/0.51          | ~ (v3_ordinal1 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('76', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X17)
% 0.20/0.51          | ~ (r4_wellord1 @ X17 @ 
% 0.20/0.51               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.20/0.51           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('82', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.20/0.51           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '83'])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t50_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v1_relat_1 @ B ) =>
% 0.20/0.51           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X12)
% 0.20/0.51          | (r4_wellord1 @ X12 @ X13)
% 0.20/0.51          | ~ (r4_wellord1 @ X13 @ X12)
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.51  thf('89', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('90', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.51  thf(t52_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v1_relat_1 @ B ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( v1_relat_1 @ C ) =>
% 0.20/0.51               ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.20/0.51                 ( r4_wellord1 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X14)
% 0.20/0.51          | ~ (r4_wellord1 @ X15 @ X14)
% 0.20/0.51          | ~ (r4_wellord1 @ X14 @ X16)
% 0.20/0.51          | (r4_wellord1 @ X15 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('95', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['85', '96'])).
% 0.20/0.51  thf('98', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.51  thf('100', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['84', '99', '100', '101'])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['102'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '105'])).
% 0.20/0.51  thf('107', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('108', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['106', '107'])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X5)
% 0.20/0.51          | ~ (v3_ordinal1 @ X6)
% 0.20/0.51          | (r1_tarski @ X5 @ X6)
% 0.20/0.51          | ~ (r1_ordinal1 @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.51  thf('111', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('112', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('113', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i]:
% 0.20/0.51         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.20/0.51          | ~ (r1_tarski @ X27 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.51  thf('116', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1)
% 0.20/0.51           = (k2_wellord1 @ (k2_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('117', plain,
% 0.20/0.51      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)
% 0.20/0.51         = (k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B))),
% 0.20/0.51      inference('sup+', [status(thm)], ['115', '116'])).
% 0.20/0.51  thf('118', plain,
% 0.20/0.51      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.51  thf('119', plain,
% 0.20/0.51      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['117', '118'])).
% 0.20/0.51  thf('120', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.20/0.51             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r2_hidden @ X1 @ X0)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '55'])).
% 0.20/0.51  thf('121', plain,
% 0.20/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.51  thf('122', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.51  thf('123', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('124', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X14)
% 0.20/0.51          | ~ (r4_wellord1 @ X15 @ X14)
% 0.20/0.51          | ~ (r4_wellord1 @ X14 @ X16)
% 0.20/0.51          | (r4_wellord1 @ X15 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.20/0.51  thf('125', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['123', '124'])).
% 0.20/0.51  thf('126', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('127', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('128', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r4_wellord1 @ (k1_wellord2 @ sk_A) @ X0)
% 0.20/0.51          | ~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.20/0.51  thf('129', plain,
% 0.20/0.51      (((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['122', '128'])).
% 0.20/0.51  thf('130', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('131', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['129', '130'])).
% 0.20/0.51  thf('132', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('133', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('134', plain,
% 0.20/0.51      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['121', '131', '132', '133'])).
% 0.20/0.51  thf('135', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('136', plain,
% 0.20/0.51      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 0.20/0.51  thf('137', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '136'])).
% 0.20/0.51  thf('138', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('139', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['137', '138'])).
% 0.20/0.51  thf('140', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '139'])).
% 0.20/0.51  thf('141', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('142', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('143', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.51        | ((sk_B) = (sk_A))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.20/0.51  thf('144', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.51      inference('simplify', [status(thm)], ['143'])).
% 0.20/0.51  thf('145', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('146', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.51  thf('147', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X24)
% 0.20/0.51          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.20/0.51          | ~ (r2_hidden @ X25 @ X24)
% 0.20/0.51          | ~ (v3_ordinal1 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.20/0.51  thf('148', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['146', '147'])).
% 0.20/0.51  thf('149', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('150', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('151', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.20/0.51  thf('152', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X17)
% 0.20/0.51          | ~ (r4_wellord1 @ X17 @ 
% 0.20/0.51               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.20/0.51  thf('153', plain,
% 0.20/0.51      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 0.20/0.51           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.20/0.51        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.51  thf('154', plain,
% 0.20/0.51      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.51  thf('155', plain,
% 0.20/0.51      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.51  thf('156', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.51  thf('157', plain,
% 0.20/0.51      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('158', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.20/0.51  thf('159', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['153', '154', '155', '156', '157', '158'])).
% 0.20/0.51  thf('160', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '159'])).
% 0.20/0.51  thf('161', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('162', plain, ($false), inference('demod', [status(thm)], ['160', '161'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
