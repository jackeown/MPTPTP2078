%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I7Gp0S1B48

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:15 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 193 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   20
%              Number of atoms          :  715 (1362 expanded)
%              Number of equality atoms :   79 ( 141 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i] :
      ( ~ ( v1_zfmisc_1 @ X41 )
      | ( X41
        = ( k6_domain_1 @ X41 @ ( sk_B_1 @ X41 ) ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X41: $i] :
      ( ~ ( v1_zfmisc_1 @ X41 )
      | ( m1_subset_1 @ ( sk_B_1 @ X41 ) @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( ( k6_domain_1 @ X39 @ X40 )
        = ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_A )
    = ( k5_xboole_0 @ sk_B_2 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference(demod,[status(thm)],['10','15'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['16','21'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = X33 )
      | ( ( k1_tarski @ X34 )
       != ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['32','33'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('60',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['32','33'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('65',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_2 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('73',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['26','62','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','75'])).

thf('77',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect+',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I7Gp0S1B48
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.15/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.34  % Solved by: fo/fo7.sh
% 1.15/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.34  % done 1806 iterations in 0.889s
% 1.15/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.34  % SZS output start Refutation
% 1.15/1.34  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.15/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.34  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.15/1.34  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.15/1.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.15/1.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.34  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.34  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.15/1.34  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(sk_B_type, type, sk_B: $i > $i).
% 1.15/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.15/1.34  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.15/1.34  thf(t1_tex_2, conjecture,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.34       ( ![B:$i]:
% 1.15/1.34         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.15/1.34           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.34    (~( ![A:$i]:
% 1.15/1.34        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.34          ( ![B:$i]:
% 1.15/1.34            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.15/1.34              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 1.15/1.34    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 1.15/1.34  thf('0', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(d1_tex_2, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.34       ( ( v1_zfmisc_1 @ A ) <=>
% 1.15/1.34         ( ?[B:$i]:
% 1.15/1.34           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 1.15/1.34  thf('1', plain,
% 1.15/1.34      (![X41 : $i]:
% 1.15/1.34         (~ (v1_zfmisc_1 @ X41)
% 1.15/1.34          | ((X41) = (k6_domain_1 @ X41 @ (sk_B_1 @ X41)))
% 1.15/1.34          | (v1_xboole_0 @ X41))),
% 1.15/1.34      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.15/1.34  thf('2', plain,
% 1.15/1.34      (![X41 : $i]:
% 1.15/1.34         (~ (v1_zfmisc_1 @ X41)
% 1.15/1.34          | (m1_subset_1 @ (sk_B_1 @ X41) @ X41)
% 1.15/1.34          | (v1_xboole_0 @ X41))),
% 1.15/1.34      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.15/1.34  thf(redefinition_k6_domain_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.15/1.34       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.15/1.34  thf('3', plain,
% 1.15/1.34      (![X39 : $i, X40 : $i]:
% 1.15/1.34         ((v1_xboole_0 @ X39)
% 1.15/1.34          | ~ (m1_subset_1 @ X40 @ X39)
% 1.15/1.34          | ((k6_domain_1 @ X39 @ X40) = (k1_tarski @ X40)))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.15/1.34  thf('4', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((v1_xboole_0 @ X0)
% 1.15/1.34          | ~ (v1_zfmisc_1 @ X0)
% 1.15/1.34          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.15/1.34          | (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.34  thf('5', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 1.15/1.34          | ~ (v1_zfmisc_1 @ X0)
% 1.15/1.34          | (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('simplify', [status(thm)], ['4'])).
% 1.15/1.34  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(l32_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.15/1.34  thf('7', plain,
% 1.15/1.34      (![X13 : $i, X15 : $i]:
% 1.15/1.34         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 1.15/1.34          | ~ (r1_tarski @ X13 @ X15))),
% 1.15/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.15/1.34  thf('8', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.34  thf(t98_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.15/1.34  thf('9', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X20 @ X21)
% 1.15/1.34           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.15/1.34  thf('10', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B_2 @ sk_A) = (k5_xboole_0 @ sk_B_2 @ k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['8', '9'])).
% 1.15/1.34  thf(t4_boole, axiom,
% 1.15/1.34    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.15/1.34  thf('11', plain,
% 1.15/1.34      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 1.15/1.34      inference('cnf', [status(esa)], [t4_boole])).
% 1.15/1.34  thf('12', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X20 @ X21)
% 1.15/1.34           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.15/1.34  thf('13', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['11', '12'])).
% 1.15/1.34  thf(t1_boole, axiom,
% 1.15/1.34    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.15/1.34  thf('14', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.15/1.34      inference('cnf', [status(esa)], [t1_boole])).
% 1.15/1.34  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['13', '14'])).
% 1.15/1.34  thf('16', plain, (((k2_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 1.15/1.34      inference('demod', [status(thm)], ['10', '15'])).
% 1.15/1.34  thf(commutativity_k2_tarski, axiom,
% 1.15/1.34    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.15/1.34  thf('17', plain,
% 1.15/1.34      (![X22 : $i, X23 : $i]:
% 1.15/1.34         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.15/1.34  thf(l51_zfmisc_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.15/1.34  thf('18', plain,
% 1.15/1.34      (![X30 : $i, X31 : $i]:
% 1.15/1.34         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 1.15/1.34      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.15/1.34  thf('19', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['17', '18'])).
% 1.15/1.34  thf('20', plain,
% 1.15/1.34      (![X30 : $i, X31 : $i]:
% 1.15/1.34         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 1.15/1.34      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.15/1.34  thf('21', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['19', '20'])).
% 1.15/1.34  thf('22', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 1.15/1.34      inference('demod', [status(thm)], ['16', '21'])).
% 1.15/1.34  thf(t44_zfmisc_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.15/1.34          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.15/1.34          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 1.15/1.34  thf('23', plain,
% 1.15/1.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.15/1.34         (((X32) = (k1_xboole_0))
% 1.15/1.34          | ((X33) = (k1_xboole_0))
% 1.15/1.34          | ((X32) = (X33))
% 1.15/1.34          | ((k1_tarski @ X34) != (k2_xboole_0 @ X32 @ X33)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 1.15/1.34  thf('24', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((k1_tarski @ X0) != (sk_B_2))
% 1.15/1.34          | ((sk_A) = (sk_B_2))
% 1.15/1.34          | ((sk_B_2) = (k1_xboole_0))
% 1.15/1.34          | ((sk_A) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['22', '23'])).
% 1.15/1.34  thf('25', plain, (((sk_A) != (sk_B_2))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('26', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((k1_tarski @ X0) != (sk_B_2))
% 1.15/1.34          | ((sk_B_2) = (k1_xboole_0))
% 1.15/1.34          | ((sk_A) = (k1_xboole_0)))),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 1.15/1.34  thf(d1_xboole_0, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.15/1.34  thf('27', plain,
% 1.15/1.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.15/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.15/1.34  thf('28', plain,
% 1.15/1.34      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.15/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.15/1.34  thf('29', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(d3_tarski, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( r1_tarski @ A @ B ) <=>
% 1.15/1.34       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.15/1.34  thf('30', plain,
% 1.15/1.34      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X3 @ X4)
% 1.15/1.34          | (r2_hidden @ X3 @ X5)
% 1.15/1.34          | ~ (r1_tarski @ X4 @ X5))),
% 1.15/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.15/1.34  thf('31', plain,
% 1.15/1.34      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['29', '30'])).
% 1.15/1.34  thf('32', plain,
% 1.15/1.34      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 1.15/1.34      inference('sup-', [status(thm)], ['28', '31'])).
% 1.15/1.34  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('34', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 1.15/1.34      inference('clc', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf(d4_xboole_0, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.15/1.34       ( ![D:$i]:
% 1.15/1.34         ( ( r2_hidden @ D @ C ) <=>
% 1.15/1.34           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.15/1.34  thf('35', plain,
% 1.15/1.34      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X7 @ X8)
% 1.15/1.34          | ~ (r2_hidden @ X7 @ X9)
% 1.15/1.34          | (r2_hidden @ X7 @ X10)
% 1.15/1.34          | ((X10) != (k3_xboole_0 @ X8 @ X9)))),
% 1.15/1.34      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.15/1.34  thf('36', plain,
% 1.15/1.34      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.15/1.34         ((r2_hidden @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 1.15/1.34          | ~ (r2_hidden @ X7 @ X9)
% 1.15/1.34          | ~ (r2_hidden @ X7 @ X8))),
% 1.15/1.34      inference('simplify', [status(thm)], ['35'])).
% 1.15/1.34  thf('37', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (r2_hidden @ (sk_B @ sk_A) @ X0)
% 1.15/1.34          | (r2_hidden @ (sk_B @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B_2)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['34', '36'])).
% 1.15/1.34  thf('38', plain,
% 1.15/1.34      (((v1_xboole_0 @ sk_A)
% 1.15/1.34        | (r2_hidden @ (sk_B @ sk_A) @ (k3_xboole_0 @ sk_A @ sk_B_2)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['27', '37'])).
% 1.15/1.34  thf('39', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(t28_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.15/1.34  thf('40', plain,
% 1.15/1.34      (![X17 : $i, X18 : $i]:
% 1.15/1.34         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.15/1.34      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.34  thf('41', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['39', '40'])).
% 1.15/1.34  thf('42', plain,
% 1.15/1.34      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['38', '41'])).
% 1.15/1.34  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('44', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 1.15/1.34      inference('clc', [status(thm)], ['42', '43'])).
% 1.15/1.34  thf('45', plain,
% 1.15/1.34      (![X4 : $i, X6 : $i]:
% 1.15/1.34         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.15/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.15/1.34  thf(d1_tarski, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.15/1.34       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.15/1.34  thf('46', plain,
% 1.15/1.34      (![X24 : $i, X26 : $i, X27 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X27 @ X26)
% 1.15/1.34          | ((X27) = (X24))
% 1.15/1.34          | ((X26) != (k1_tarski @ X24)))),
% 1.15/1.34      inference('cnf', [status(esa)], [d1_tarski])).
% 1.15/1.34  thf('47', plain,
% 1.15/1.34      (![X24 : $i, X27 : $i]:
% 1.15/1.34         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 1.15/1.34      inference('simplify', [status(thm)], ['46'])).
% 1.15/1.34  thf('48', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.15/1.34          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['45', '47'])).
% 1.15/1.34  thf('49', plain,
% 1.15/1.34      (![X4 : $i, X6 : $i]:
% 1.15/1.34         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.15/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.15/1.34  thf('50', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (r2_hidden @ X0 @ X1)
% 1.15/1.34          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.15/1.34          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['48', '49'])).
% 1.15/1.34  thf('51', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.15/1.34      inference('simplify', [status(thm)], ['50'])).
% 1.15/1.34  thf('52', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A)),
% 1.15/1.34      inference('sup-', [status(thm)], ['44', '51'])).
% 1.15/1.34  thf('53', plain,
% 1.15/1.34      (![X13 : $i, X15 : $i]:
% 1.15/1.34         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 1.15/1.34          | ~ (r1_tarski @ X13 @ X15))),
% 1.15/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.15/1.34  thf('54', plain,
% 1.15/1.34      (((k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_A) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['52', '53'])).
% 1.15/1.34  thf('55', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X20 @ X21)
% 1.15/1.34           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.15/1.34  thf('56', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_A @ (k1_tarski @ (sk_B @ sk_A)))
% 1.15/1.34         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['54', '55'])).
% 1.15/1.34  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['13', '14'])).
% 1.15/1.34  thf('58', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_A @ (k1_tarski @ (sk_B @ sk_A))) = (sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['56', '57'])).
% 1.15/1.34  thf('59', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['19', '20'])).
% 1.15/1.34  thf(t49_zfmisc_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.15/1.34  thf('60', plain,
% 1.15/1.34      (![X35 : $i, X36 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k1_tarski @ X35) @ X36) != (k1_xboole_0))),
% 1.15/1.34      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.15/1.34  thf('61', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['59', '60'])).
% 1.15/1.34  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['58', '61'])).
% 1.15/1.34  thf('63', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 1.15/1.34      inference('clc', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('64', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.15/1.34      inference('simplify', [status(thm)], ['50'])).
% 1.15/1.34  thf('65', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)),
% 1.15/1.34      inference('sup-', [status(thm)], ['63', '64'])).
% 1.15/1.34  thf('66', plain,
% 1.15/1.34      (![X13 : $i, X15 : $i]:
% 1.15/1.34         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 1.15/1.34          | ~ (r1_tarski @ X13 @ X15))),
% 1.15/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.15/1.34  thf('67', plain,
% 1.15/1.34      (((k4_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['65', '66'])).
% 1.15/1.34  thf('68', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X20 @ X21)
% 1.15/1.34           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.15/1.34  thf('69', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B_2 @ (k1_tarski @ (sk_B @ sk_A)))
% 1.15/1.34         = (k5_xboole_0 @ sk_B_2 @ k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['67', '68'])).
% 1.15/1.34  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['13', '14'])).
% 1.15/1.34  thf('71', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B_2 @ (k1_tarski @ (sk_B @ sk_A))) = (sk_B_2))),
% 1.15/1.34      inference('demod', [status(thm)], ['69', '70'])).
% 1.15/1.34  thf('72', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['59', '60'])).
% 1.15/1.34  thf('73', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['71', '72'])).
% 1.15/1.34  thf('74', plain, (![X0 : $i]: ((k1_tarski @ X0) != (sk_B_2))),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['26', '62', '73'])).
% 1.15/1.34  thf('75', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) != (sk_B_2))
% 1.15/1.34          | (v1_xboole_0 @ X0)
% 1.15/1.34          | ~ (v1_zfmisc_1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '74'])).
% 1.15/1.34  thf('76', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((X0) != (sk_B_2))
% 1.15/1.34          | (v1_xboole_0 @ X0)
% 1.15/1.34          | ~ (v1_zfmisc_1 @ X0)
% 1.15/1.34          | ~ (v1_zfmisc_1 @ X0)
% 1.15/1.34          | (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['1', '75'])).
% 1.15/1.34  thf('77', plain, ((~ (v1_zfmisc_1 @ sk_B_2) | (v1_xboole_0 @ sk_B_2))),
% 1.15/1.34      inference('simplify', [status(thm)], ['76'])).
% 1.15/1.34  thf('78', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('79', plain, ((v1_xboole_0 @ sk_B_2)),
% 1.15/1.34      inference('simplify_reflect+', [status(thm)], ['77', '78'])).
% 1.15/1.34  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 1.15/1.34  
% 1.15/1.34  % SZS output end Refutation
% 1.15/1.34  
% 1.15/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
