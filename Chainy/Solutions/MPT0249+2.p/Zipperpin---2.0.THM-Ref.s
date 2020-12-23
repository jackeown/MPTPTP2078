%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0249+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.94oEvigcwT

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 10.84s
% Output     : Refutation 10.84s
% Verified   : 
% Statistics : Number of formulae       :  188 (2083 expanded)
%              Number of leaves         :   49 ( 679 expanded)
%              Depth                    :   29
%              Number of atoms          : 1140 (15905 expanded)
%              Number of equality atoms :  132 (2185 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ ( B @ C ) ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ ( B @ C ) ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X993: $i,X994: $i] :
      ( ( r2_hidden @ ( X993 @ X994 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X993 @ X994 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( X21 @ X19 ) )
      | ( r2_hidden @ ( X21 @ X20 ) )
      | ( r2_hidden @ ( X21 @ X18 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( X21 @ X18 ) )
      | ( r2_hidden @ ( X21 @ X20 ) )
      | ~ ( r2_hidden @ ( X21 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r1_tarski @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('13',plain,(
    ! [X158: $i,X159: $i,X160: $i] :
      ( ( r1_tarski @ ( X158 @ X159 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X158 @ X160 ) @ X159 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r1_tarski @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X998: $i,X999: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X999 @ X998 ) )
        = X998 )
      | ~ ( r2_hidden @ ( X999 @ X998 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('16',plain,
    ( ( r1_tarski @ ( sk_B_2 @ sk_C_10 ) )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X272: $i,X273: $i,X274: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X272 @ X273 ) @ X274 ) )
      = ( k2_xboole_0 @ ( X272 @ ( k2_xboole_0 @ ( X273 @ X274 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('22',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('25',plain,(
    ! [X192: $i,X193: $i] :
      ( ( k2_xboole_0 @ ( X192 @ ( k3_xboole_0 @ ( X192 @ X193 ) ) ) )
      = X192 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,
    ( ( r1_tarski @ ( sk_B_2 @ sk_C_10 ) )
    | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['16','17','18','19','30','31'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('33',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
    | ( sk_B_2 = sk_C_10 )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B_2 != sk_C_10 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('42',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) )
      | ( X0 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_C_10 )
    | ( ( sk_B @ sk_C_10 )
      = sk_A_2 ) ),
    inference('sup-',[status(thm)],['40','44'])).

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

thf('46',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('49',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('53',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('54',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('55',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ ( A @ B ) )
          = ( k2_xboole_0 @ ( C @ D ) ) )
        & ( r1_xboole_0 @ ( C @ A ) )
        & ( r1_xboole_0 @ ( D @ B ) ) )
     => ( C = B ) ) )).

thf('57',plain,(
    ! [X338: $i,X339: $i,X340: $i,X341: $i] :
      ( ( X339 = X338 )
      | ~ ( r1_xboole_0 @ ( X339 @ X340 ) )
      | ( ( k2_xboole_0 @ ( X340 @ X338 ) )
       != ( k2_xboole_0 @ ( X339 @ X341 ) ) )
      | ~ ( r1_xboole_0 @ ( X341 @ X338 ) ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ ( X2 @ X1 ) )
       != X0 )
      | ~ ( r1_xboole_0 @ ( X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ ( o_0_0_xboole_0 @ X2 ) )
      | ( o_0_0_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ ( A @ k1_xboole_0 ) )
      = k1_xboole_0 ) )).

thf('60',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('62',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('63',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ o_0_0_xboole_0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','63'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('65',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('67',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ ( X2 @ X1 ) )
       != X0 )
      | ~ ( r1_xboole_0 @ ( X0 @ X1 ) )
      | ( o_0_0_xboole_0 = X1 ) ) ),
    inference(demod,[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X1: $i,X2: $i] :
      ( ( o_0_0_xboole_0 = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( X2 @ X1 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( r1_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    | ( o_0_0_xboole_0 = sk_C_10 ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,(
    sk_C_10 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('75',plain,(
    sk_C_10 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ sk_C_10 )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['50','76'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('78',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf('81',plain,(
    ! [X306: $i,X307: $i] :
      ( ~ ( r1_tarski @ ( X306 @ X307 ) )
      | ~ ( r2_xboole_0 @ ( X307 @ X306 ) ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_C_10 ) ),
    inference(clc,[status(thm)],['77','82'])).

thf('84',plain,
    ( ( sk_B @ sk_C_10 )
    = sk_A_2 ),
    inference(clc,[status(thm)],['45','83'])).

thf('85',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
    | ( v1_xboole_0 @ sk_C_10 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_C_10 ) ),
    inference(clc,[status(thm)],['77','82'])).

thf('88',plain,(
    r2_hidden @ ( sk_A_2 @ sk_C_10 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X998: $i,X999: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X999 @ X998 ) )
        = X998 )
      | ~ ( r2_hidden @ ( X999 @ X998 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('90',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_C_10 ) )
    = sk_C_10 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X272: $i,X273: $i,X274: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X272 @ X273 ) @ X274 ) )
      = ( k2_xboole_0 @ ( X272 @ ( k2_xboole_0 @ ( X273 @ X274 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('93',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    = sk_C_10 ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( sk_B_2 = sk_C_10 )
    | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['36','94'])).

thf('96',plain,(
    sk_B_2 != sk_C_10 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ~ ( r2_hidden @ ( C @ A ) ) ) ) )).

thf('98',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('99',plain,(
    r2_hidden @ ( sk_C_4 @ ( sk_C_10 @ sk_B_2 ) @ sk_C_10 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) )
      | ( X0 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('101',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    = sk_C_10 ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ sk_C_10 ) )
      | ( X0 = sk_A_2 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('104',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ ( B @ C ) ) )
     => ( A = B ) ) )).

thf('105',plain,(
    ! [X1135: $i,X1136: $i,X1137: $i] :
      ( ( X1136 = X1135 )
      | ( ( k1_tarski @ X1136 )
       != ( k2_tarski @ ( X1135 @ X1137 ) ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
       != ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['106'])).

thf('108',plain,
    ( ( '#_fresh_sk3' @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['103','107'])).

thf('109',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    = sk_C_10 ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('110',plain,
    ( ( '#_fresh_sk3' @ sk_C_10 )
    = sk_A_2 ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ sk_C_10 ) )
      | ( X0
        = ( '#_fresh_sk3' @ sk_C_10 ) ) ) ),
    inference(demod,[status(thm)],['102','110'])).

thf('112',plain,
    ( ( sk_C_4 @ ( sk_C_10 @ sk_B_2 ) )
    = ( '#_fresh_sk3' @ sk_C_10 ) ),
    inference('sup-',[status(thm)],['99','111'])).

thf('113',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ~ ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('114',plain,
    ( ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) )
    | ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('116',plain,(
    ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('117',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('118',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('119',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    = sk_C_10 ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('121',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('122',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['120','121'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('123',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( X27 @ X26 ) )
      | ( r2_hidden @ ( X27 @ X25 ) )
      | ( X26
       != ( k3_xboole_0 @ ( X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('124',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ ( X27 @ X25 ) )
      | ~ ( r2_hidden @ ( X27 @ ( k3_xboole_0 @ ( X24 @ X25 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ sk_B_2 ) )
      | ( r2_hidden @ ( X0 @ sk_C_10 ) ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('126',plain,
    ( ( sk_B_2 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('129',plain,(
    sk_B_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    r2_hidden @ ( sk_B_1 @ sk_B_2 @ sk_C_10 ) ),
    inference('simplify_reflect-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ sk_C_10 ) )
      | ( X0
        = ( '#_fresh_sk3' @ sk_C_10 ) ) ) ),
    inference(demod,[status(thm)],['102','110'])).

thf('132',plain,
    ( ( sk_B_1 @ sk_B_2 )
    = ( '#_fresh_sk3' @ sk_C_10 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('134',plain,
    ( ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) )
    | ( sk_B_2 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    sk_B_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['127','128'])).

thf('136',plain,(
    r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['116','136'])).

%------------------------------------------------------------------------------
