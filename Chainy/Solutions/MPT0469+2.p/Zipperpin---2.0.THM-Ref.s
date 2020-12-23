%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0469+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XhMiOkQy8R

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 49.81s
% Output     : Refutation 49.81s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 717 expanded)
%              Number of leaves         :   60 ( 247 expanded)
%              Depth                    :   28
%              Number of atoms          : 1473 (4369 expanded)
%              Number of equality atoms :  160 ( 630 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_16_type,type,(
    sk_C_16: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t136_zfmisc_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ ( C @ B ) )
            & ~ ( r2_tarski @ ( C @ B ) )
            & ~ ( r2_hidden @ ( C @ B ) ) )
      & ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
         => ( r2_hidden @ ( k1_zfmisc_1 @ C @ B ) ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ ( C @ B ) )
            & ( r1_tarski @ ( D @ C ) ) )
         => ( r2_hidden @ ( D @ B ) ) )
      & ( r2_hidden @ ( A @ B ) ) ) )).

thf('0',plain,(
    ! [X1181: $i] :
      ( r2_hidden @ ( X1181 @ ( sk_B_3 @ X1181 ) ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( X1 @ ( sk_B_3 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t32_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( A @ B ) ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X2141: $i,X2142: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X2141 @ X2142 ) ) ) )
      = ( k2_tarski @ ( X2141 @ X2142 ) ) ) ),
    inference(cnf,[status(esa)],[t32_relat_1])).

thf(t33_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k3_relat_1 @ ( k2_xboole_0 @ ( A @ B ) ) )
            = ( k2_xboole_0 @ ( k3_relat_1 @ A @ ( k3_relat_1 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X2143: $i,X2144: $i] :
      ( ~ ( v1_relat_1 @ X2143 )
      | ( ( k3_relat_1 @ ( k2_xboole_0 @ ( X2144 @ X2143 ) ) )
        = ( k2_xboole_0 @ ( k3_relat_1 @ X2144 @ ( k3_relat_1 @ X2143 ) ) ) )
      | ~ ( v1_relat_1 @ X2144 ) ) ),
    inference(cnf,[status(esa)],[t33_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('6',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X363: $i,X364: $i] :
      ( r1_tarski @ ( X363 @ ( k2_xboole_0 @ ( X363 @ X364 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('12',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( X1 @ X0 ) ) )
      | ( r2_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      | ( o_0_0_xboole_0
        = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X86: $i,X87: $i] :
      ( ( v1_xboole_0 @ X86 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( X87 @ X86 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( r2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

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

thf('22',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( X0 != o_0_0_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ o_0_0_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ o_0_0_xboole_0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ ( k2_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X1104: $i,X1105: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1104 @ X1105 ) )
        = k1_xboole_0 )
      | ( X1104 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( k1_xboole_0 @ X1105 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ X1105 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('37',plain,(
    ! [X2096: $i,X2097: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2096 @ X2097 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('41',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('45',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ ( A @ B ) ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A @ ( k4_relat_1 @ B ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X2153: $i,X2154: $i] :
      ( ~ ( v1_relat_1 @ X2153 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ ( X2154 @ X2153 ) ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X2154 @ ( k4_relat_1 @ X2153 ) ) ) )
      | ~ ( v1_relat_1 @ X2154 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k6_subset_1 @ ( X0 @ X0 ) ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['38','51'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X2147: $i] :
      ( ( ( k2_relat_1 @ X2147 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2147 ) ) )
      | ~ ( v1_relat_1 @ X2147 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('54',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
      = ( k1_relat_1 @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('56',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X2070: $i] :
      ( ( ( k3_relat_1 @ X2070 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X2070 @ ( k2_relat_1 @ X2070 ) ) ) )
      | ~ ( v1_relat_1 @ X2070 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('59',plain,
    ( ( ( k3_relat_1 @ o_0_0_xboole_0 )
      = ( k2_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('60',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('61',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('62',plain,
    ( ( k3_relat_1 @ o_0_0_xboole_0 )
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = ( k3_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,
    ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','63'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ~ ( r2_hidden @ ( C @ A ) ) ) ) )).

thf('65',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k2_xboole_0 @ ( X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k3_relat_1 @ ( k2_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ) ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','68'])).

thf('70',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('71',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k3_relat_1 @ X0 ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k2_tarski @ ( X1 @ X0 ) ) ) )
        | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X1 @ X0 ) ) ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','72'])).

thf(fc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( A @ B ) ) ) ) )).

thf('74',plain,(
    ! [X2094: $i,X2095: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X2094 @ X2095 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc5_relat_1])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k2_tarski @ ( X1 @ X0 ) ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('77',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('78',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('81',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( X0 != o_0_0_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ ( k1_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,
    ( ( k3_relat_1 @ o_0_0_xboole_0 )
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('88',plain,
    ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('90',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
        = B ) ) )).

thf('91',plain,(
    ! [X1026: $i,X1027: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1027 @ X1026 ) )
        = X1026 )
      | ~ ( r2_hidden @ ( X1027 @ X1026 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('92',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
      = ( k3_relat_1 @ o_0_0_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,
    ( ( ( k2_xboole_0 @ ( k3_relat_1 @ o_0_0_xboole_0 @ ( k1_tarski @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ) ) )
      = ( k3_relat_1 @ o_0_0_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ ( A @ B ) )
     => ( r1_xboole_0 @ ( k1_tarski @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X1030: $i,X1031: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1030 @ X1031 ) )
      | ( r2_hidden @ ( X1030 @ X1031 ) ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ ( A @ B ) )
              & ( r1_xboole_0 @ ( A @ C ) ) )
          & ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('96',plain,(
    ! [X331: $i,X332: $i,X334: $i] :
      ( ( r1_xboole_0 @ ( X331 @ X332 ) )
      | ~ ( r1_xboole_0 @ ( X331 @ ( k2_xboole_0 @ ( X332 @ X334 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
        | ( r1_xboole_0 @ ( k1_tarski @ X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('99',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('100',plain,(
    ! [X2141: $i,X2142: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X2141 @ X2142 ) ) ) )
      = ( k2_tarski @ ( X2141 @ X2142 ) ) ) ),
    inference(cnf,[status(esa)],[t32_relat_1])).

thf('101',plain,(
    ! [X2143: $i,X2144: $i] :
      ( ~ ( v1_relat_1 @ X2143 )
      | ( ( k3_relat_1 @ ( k2_xboole_0 @ ( X2144 @ X2143 ) ) )
        = ( k2_xboole_0 @ ( k3_relat_1 @ X2144 @ ( k3_relat_1 @ X2143 ) ) ) )
      | ~ ( v1_relat_1 @ X2144 ) ) ),
    inference(cnf,[status(esa)],[t33_relat_1])).

thf('102',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('103',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('104',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k2_xboole_0 @ ( X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('106',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ ( X60 @ X58 ) )
      | ~ ( r2_hidden @ ( X60 @ X61 ) )
      | ~ ( r1_xboole_0 @ ( X58 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('107',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) @ X1 ) )
        | ~ ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ X1 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k3_relat_1 @ ( k2_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('111',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k3_relat_1 @ X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_tarski @ ( X1 @ X0 ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
        | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X1 @ X0 ) ) ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    ! [X2094: $i,X2095: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X2094 @ X2095 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc5_relat_1])).

thf('115',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r1_xboole_0 @ ( k2_tarski @ ( X1 @ X0 ) @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ~ ( r1_xboole_0 @ ( k1_tarski @ X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( X0 @ ( k3_relat_1 @ o_0_0_xboole_0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','116'])).

thf('118',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('119',plain,(
    ! [X1021: $i,X1022: $i] :
      ( ( r2_hidden @ ( X1021 @ X1022 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X1021 @ X1022 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('121',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('122',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('123',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ ( D @ B ) )
                    & ( r2_hidden @ ( D @ C ) ) ) ) ) )).

thf('124',plain,(
    ! [X1416: $i,X1417: $i] :
      ( ~ ( r2_hidden @ ( X1416 @ X1417 ) )
      | ( r2_hidden @ ( sk_C_16 @ X1417 @ X1417 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_C_16 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('126',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('127',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = o_0_0_xboole_0 )
      | ( ( sk_C_16 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
     != k1_xboole_0 ) )).

thf('130',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('131',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('132',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( sk_C_16 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['128','133'])).

thf('135',plain,(
    ! [X1416: $i,X1417: $i,X1418: $i] :
      ( ~ ( r2_hidden @ ( X1416 @ X1417 ) )
      | ~ ( r2_hidden @ ( X1418 @ X1417 ) )
      | ~ ( r2_hidden @ ( X1418 @ ( sk_C_16 @ X1417 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ ( sk_C_16 @ X0 ) ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ X0 ) )
      | ~ ( r2_hidden @ ( X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','137'])).

thf('139',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','138'])).

thf('140',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('141',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['75','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_C_16 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('144',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('145',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X0 @ X0 ) ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ ( X0 @ X0 ) )
        = o_0_0_xboole_0 )
      | ( ( sk_C_16 @ ( k2_tarski @ ( X0 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) )
     != k1_xboole_0 ) )).

thf('149',plain,(
    ! [X1345: $i,X1346: $i,X1347: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ ( X1345 @ X1346 ) @ X1347 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('150',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('151',plain,(
    ! [X1345: $i,X1346: $i,X1347: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ ( X1345 @ X1346 ) @ X1347 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ ( X1 @ X0 ) )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( sk_C_16 @ ( k2_tarski @ ( X0 @ X0 ) ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ ( sk_C_16 @ X0 ) ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['135'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ X0 ) )
      | ~ ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_C_4 @ ( k3_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','155'])).

thf('157',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','156'])).

%------------------------------------------------------------------------------
