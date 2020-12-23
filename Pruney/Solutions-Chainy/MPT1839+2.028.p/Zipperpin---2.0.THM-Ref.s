%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SYpWZD4zyS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:26 EST 2020

% Result     : Theorem 22.02s
% Output     : Refutation 22.02s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 747 expanded)
%              Number of leaves         :   36 ( 245 expanded)
%              Depth                    :   32
%              Number of atoms          : 1105 (5362 expanded)
%              Number of equality atoms :  111 ( 610 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X23 ) )
      | ( ( sk_C_2 @ X27 @ X23 )
        = X23 )
      | ( r2_hidden @ ( sk_C_2 @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('18',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X23 ) )
      | ( ( sk_C_2 @ X27 @ X23 )
       != X23 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
       != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','19'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['32','37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['47','50'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('52',plain,(
    ! [X50: $i] :
      ( ~ ( v1_zfmisc_1 @ X50 )
      | ( X50
        = ( k6_domain_1 @ X50 @ ( sk_B_1 @ X50 ) ) )
      | ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('53',plain,(
    ! [X50: $i] :
      ( ~ ( v1_zfmisc_1 @ X50 )
      | ( m1_subset_1 @ ( sk_B_1 @ X50 ) @ X50 )
      | ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('54',plain,(
    ! [X48: $i,X49: $i] :
      ( ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ X48 )
      | ( ( k6_domain_1 @ X48 @ X49 )
        = ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
      = ( sk_B_1 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
      = ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X24 != X23 )
      | ( r2_hidden @ X24 @ X25 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('69',plain,(
    ! [X23: $i] :
      ( r2_hidden @ X23 @ ( k1_tarski @ X23 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['67','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('78',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( k1_tarski @ X0 )
        = X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = ( sk_B @ X0 ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','29'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('89',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('96',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_B @ sk_A )
    = ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
      = ( sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
    = ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_B @ sk_A )
    = ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('106',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( sk_A
    = ( k1_tarski @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['46','103','110'])).

thf('112',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('115',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('119',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('121',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('122',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('124',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_A ),
    inference(demod,[status(thm)],['119','120','125'])).

thf('127',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('130',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('132',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['0','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SYpWZD4zyS
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:35:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 22.02/22.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.02/22.23  % Solved by: fo/fo7.sh
% 22.02/22.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.02/22.23  % done 24117 iterations in 21.772s
% 22.02/22.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.02/22.23  % SZS output start Refutation
% 22.02/22.23  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 22.02/22.23  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 22.02/22.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 22.02/22.23  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 22.02/22.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.02/22.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.02/22.23  thf(sk_B_type, type, sk_B: $i > $i).
% 22.02/22.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 22.02/22.23  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 22.02/22.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 22.02/22.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 22.02/22.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 22.02/22.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 22.02/22.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 22.02/22.23  thf(sk_A_type, type, sk_A: $i).
% 22.02/22.23  thf(sk_B_2_type, type, sk_B_2: $i).
% 22.02/22.23  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 22.02/22.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.02/22.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 22.02/22.23  thf(t2_tex_2, conjecture,
% 22.02/22.23    (![A:$i]:
% 22.02/22.23     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 22.02/22.23       ( ![B:$i]:
% 22.02/22.23         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 22.02/22.23           ( r1_tarski @ A @ B ) ) ) ))).
% 22.02/22.23  thf(zf_stmt_0, negated_conjecture,
% 22.02/22.23    (~( ![A:$i]:
% 22.02/22.23        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 22.02/22.23          ( ![B:$i]:
% 22.02/22.23            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 22.02/22.23              ( r1_tarski @ A @ B ) ) ) ) )),
% 22.02/22.23    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 22.02/22.23  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_2)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf(idempotence_k3_xboole_0, axiom,
% 22.02/22.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 22.02/22.23  thf('1', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 22.02/22.23      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 22.02/22.23  thf(t17_xboole_1, axiom,
% 22.02/22.23    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 22.02/22.23  thf('2', plain,
% 22.02/22.23      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 22.02/22.23      inference('cnf', [status(esa)], [t17_xboole_1])).
% 22.02/22.23  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 22.02/22.23      inference('sup+', [status(thm)], ['1', '2'])).
% 22.02/22.23  thf(l32_xboole_1, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.02/22.23  thf('4', plain,
% 22.02/22.23      (![X10 : $i, X12 : $i]:
% 22.02/22.23         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 22.02/22.23          | ~ (r1_tarski @ X10 @ X12))),
% 22.02/22.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 22.02/22.23  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['3', '4'])).
% 22.02/22.23  thf('6', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 22.02/22.23      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 22.02/22.23  thf(t100_xboole_1, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 22.02/22.23  thf('7', plain,
% 22.02/22.23      (![X13 : $i, X14 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X13 @ X14)
% 22.02/22.23           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 22.02/22.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.23  thf('8', plain,
% 22.02/22.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['6', '7'])).
% 22.02/22.23  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.23      inference('demod', [status(thm)], ['5', '8'])).
% 22.02/22.23  thf(t2_tarski, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 22.02/22.23       ( ( A ) = ( B ) ) ))).
% 22.02/22.23  thf('10', plain,
% 22.02/22.23      (![X8 : $i, X9 : $i]:
% 22.02/22.23         (((X9) = (X8))
% 22.02/22.23          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 22.02/22.23          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X9))),
% 22.02/22.23      inference('cnf', [status(esa)], [t2_tarski])).
% 22.02/22.23  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.23      inference('demod', [status(thm)], ['5', '8'])).
% 22.02/22.23  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 22.02/22.23  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 22.02/22.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 22.02/22.23  thf(d1_tarski, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 22.02/22.23       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 22.02/22.23  thf('13', plain,
% 22.02/22.23      (![X23 : $i, X27 : $i]:
% 22.02/22.23         (((X27) = (k1_tarski @ X23))
% 22.02/22.23          | ((sk_C_2 @ X27 @ X23) = (X23))
% 22.02/22.23          | (r2_hidden @ (sk_C_2 @ X27 @ X23) @ X27))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_tarski])).
% 22.02/22.23  thf(d1_xboole_0, axiom,
% 22.02/22.23    (![A:$i]:
% 22.02/22.23     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 22.02/22.23  thf('14', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 22.02/22.23  thf('15', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         (((sk_C_2 @ X0 @ X1) = (X1))
% 22.02/22.23          | ((X0) = (k1_tarski @ X1))
% 22.02/22.23          | ~ (v1_xboole_0 @ X0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['13', '14'])).
% 22.02/22.23  thf('16', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((k1_xboole_0) = (k1_tarski @ X0))
% 22.02/22.23          | ((sk_C_2 @ k1_xboole_0 @ X0) = (X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['12', '15'])).
% 22.02/22.23  thf(t1_boole, axiom,
% 22.02/22.23    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 22.02/22.23  thf('17', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 22.02/22.23      inference('cnf', [status(esa)], [t1_boole])).
% 22.02/22.23  thf(t49_zfmisc_1, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 22.02/22.23  thf('18', plain,
% 22.02/22.23      (![X42 : $i, X43 : $i]:
% 22.02/22.23         ((k2_xboole_0 @ (k1_tarski @ X42) @ X43) != (k1_xboole_0))),
% 22.02/22.23      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 22.02/22.23  thf('19', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['17', '18'])).
% 22.02/22.23  thf('20', plain, (![X0 : $i]: ((sk_C_2 @ k1_xboole_0 @ X0) = (X0))),
% 22.02/22.23      inference('simplify_reflect-', [status(thm)], ['16', '19'])).
% 22.02/22.23  thf('21', plain,
% 22.02/22.23      (![X23 : $i, X27 : $i]:
% 22.02/22.23         (((X27) = (k1_tarski @ X23))
% 22.02/22.23          | ((sk_C_2 @ X27 @ X23) != (X23))
% 22.02/22.23          | ~ (r2_hidden @ (sk_C_2 @ X27 @ X23) @ X27))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_tarski])).
% 22.02/22.23  thf('22', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 22.02/22.23          | ((sk_C_2 @ k1_xboole_0 @ X0) != (X0))
% 22.02/22.23          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['20', '21'])).
% 22.02/22.23  thf('23', plain, (![X0 : $i]: ((sk_C_2 @ k1_xboole_0 @ X0) = (X0))),
% 22.02/22.23      inference('simplify_reflect-', [status(thm)], ['16', '19'])).
% 22.02/22.23  thf('24', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 22.02/22.23          | ((X0) != (X0))
% 22.02/22.23          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 22.02/22.23      inference('demod', [status(thm)], ['22', '23'])).
% 22.02/22.23  thf('25', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 22.02/22.23      inference('simplify', [status(thm)], ['24'])).
% 22.02/22.23  thf('26', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['17', '18'])).
% 22.02/22.23  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 22.02/22.23      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 22.02/22.23  thf('28', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['11', '27'])).
% 22.02/22.23  thf('29', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((r2_hidden @ (sk_C_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) @ X1)
% 22.02/22.23          | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['10', '28'])).
% 22.02/22.23  thf('30', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 22.02/22.23          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 22.02/22.23      inference('sup+', [status(thm)], ['9', '29'])).
% 22.02/22.23  thf('31', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2))),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('32', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 22.02/22.23          | (r2_hidden @ 
% 22.02/22.23             (sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ 
% 22.02/22.23             (k3_xboole_0 @ sk_A @ sk_B_2)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['30', '31'])).
% 22.02/22.23  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['3', '4'])).
% 22.02/22.23  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 22.02/22.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 22.02/22.23  thf('35', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['33', '34'])).
% 22.02/22.23  thf('36', plain,
% 22.02/22.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['6', '7'])).
% 22.02/22.23  thf('37', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 22.02/22.23      inference('demod', [status(thm)], ['35', '36'])).
% 22.02/22.23  thf('38', plain,
% 22.02/22.23      ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ 
% 22.02/22.23        (k3_xboole_0 @ sk_A @ sk_B_2))),
% 22.02/22.23      inference('demod', [status(thm)], ['32', '37'])).
% 22.02/22.23  thf(d3_tarski, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( r1_tarski @ A @ B ) <=>
% 22.02/22.23       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 22.02/22.23  thf('39', plain,
% 22.02/22.23      (![X4 : $i, X6 : $i]:
% 22.02/22.23         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 22.02/22.23      inference('cnf', [status(esa)], [d3_tarski])).
% 22.02/22.23  thf('40', plain,
% 22.02/22.23      (![X23 : $i, X25 : $i, X26 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X26 @ X25)
% 22.02/22.23          | ((X26) = (X23))
% 22.02/22.23          | ((X25) != (k1_tarski @ X23)))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_tarski])).
% 22.02/22.23  thf('41', plain,
% 22.02/22.23      (![X23 : $i, X26 : $i]:
% 22.02/22.23         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 22.02/22.23      inference('simplify', [status(thm)], ['40'])).
% 22.02/22.23  thf('42', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 22.02/22.23          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['39', '41'])).
% 22.02/22.23  thf('43', plain,
% 22.02/22.23      (![X4 : $i, X6 : $i]:
% 22.02/22.23         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 22.02/22.23      inference('cnf', [status(esa)], [d3_tarski])).
% 22.02/22.23  thf('44', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X0 @ X1)
% 22.02/22.23          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 22.02/22.23          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 22.02/22.23      inference('sup-', [status(thm)], ['42', '43'])).
% 22.02/22.23  thf('45', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 22.02/22.23      inference('simplify', [status(thm)], ['44'])).
% 22.02/22.23  thf('46', plain,
% 22.02/22.23      ((r1_tarski @ 
% 22.02/22.23        (k1_tarski @ (sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2))) @ 
% 22.02/22.23        (k3_xboole_0 @ sk_A @ sk_B_2))),
% 22.02/22.23      inference('sup-', [status(thm)], ['38', '45'])).
% 22.02/22.23  thf('47', plain,
% 22.02/22.23      ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ 
% 22.02/22.23        (k3_xboole_0 @ sk_A @ sk_B_2))),
% 22.02/22.23      inference('demod', [status(thm)], ['32', '37'])).
% 22.02/22.23  thf('48', plain,
% 22.02/22.23      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 22.02/22.23      inference('cnf', [status(esa)], [t17_xboole_1])).
% 22.02/22.23  thf('49', plain,
% 22.02/22.23      (![X3 : $i, X4 : $i, X5 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X3 @ X4)
% 22.02/22.23          | (r2_hidden @ X3 @ X5)
% 22.02/22.23          | ~ (r1_tarski @ X4 @ X5))),
% 22.02/22.23      inference('cnf', [status(esa)], [d3_tarski])).
% 22.02/22.23  thf('50', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.02/22.23         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['48', '49'])).
% 22.02/22.23  thf('51', plain,
% 22.02/22.23      ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ 
% 22.02/22.23        sk_A)),
% 22.02/22.23      inference('sup-', [status(thm)], ['47', '50'])).
% 22.02/22.23  thf(d1_tex_2, axiom,
% 22.02/22.23    (![A:$i]:
% 22.02/22.23     ( ( ~( v1_xboole_0 @ A ) ) =>
% 22.02/22.23       ( ( v1_zfmisc_1 @ A ) <=>
% 22.02/22.23         ( ?[B:$i]:
% 22.02/22.23           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 22.02/22.23  thf('52', plain,
% 22.02/22.23      (![X50 : $i]:
% 22.02/22.23         (~ (v1_zfmisc_1 @ X50)
% 22.02/22.23          | ((X50) = (k6_domain_1 @ X50 @ (sk_B_1 @ X50)))
% 22.02/22.23          | (v1_xboole_0 @ X50))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_tex_2])).
% 22.02/22.23  thf('53', plain,
% 22.02/22.23      (![X50 : $i]:
% 22.02/22.23         (~ (v1_zfmisc_1 @ X50)
% 22.02/22.23          | (m1_subset_1 @ (sk_B_1 @ X50) @ X50)
% 22.02/22.23          | (v1_xboole_0 @ X50))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_tex_2])).
% 22.02/22.23  thf(redefinition_k6_domain_1, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 22.02/22.23       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 22.02/22.23  thf('54', plain,
% 22.02/22.23      (![X48 : $i, X49 : $i]:
% 22.02/22.23         ((v1_xboole_0 @ X48)
% 22.02/22.23          | ~ (m1_subset_1 @ X49 @ X48)
% 22.02/22.23          | ((k6_domain_1 @ X48 @ X49) = (k1_tarski @ X49)))),
% 22.02/22.23      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 22.02/22.23  thf('55', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         ((v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 22.02/22.23          | (v1_xboole_0 @ X0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['53', '54'])).
% 22.02/22.23  thf('56', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0))),
% 22.02/22.23      inference('simplify', [status(thm)], ['55'])).
% 22.02/22.23  thf('57', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['52', '56'])).
% 22.02/22.23  thf('58', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 22.02/22.23      inference('simplify', [status(thm)], ['57'])).
% 22.02/22.23  thf('59', plain,
% 22.02/22.23      (![X23 : $i, X26 : $i]:
% 22.02/22.23         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 22.02/22.23      inference('simplify', [status(thm)], ['40'])).
% 22.02/22.23  thf('60', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | ((X1) = (sk_B_1 @ X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['58', '59'])).
% 22.02/22.23  thf('61', plain,
% 22.02/22.23      ((((sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 22.02/22.23          = (sk_B_1 @ sk_A))
% 22.02/22.23        | ~ (v1_zfmisc_1 @ sk_A)
% 22.02/22.23        | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('sup-', [status(thm)], ['51', '60'])).
% 22.02/22.23  thf('62', plain, ((v1_zfmisc_1 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('63', plain,
% 22.02/22.23      ((((sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 22.02/22.23          = (sk_B_1 @ sk_A))
% 22.02/22.23        | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('demod', [status(thm)], ['61', '62'])).
% 22.02/22.23  thf('64', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 22.02/22.23      inference('simplify', [status(thm)], ['57'])).
% 22.02/22.23  thf('65', plain,
% 22.02/22.23      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 22.02/22.23  thf('66', plain,
% 22.02/22.23      (![X23 : $i, X26 : $i]:
% 22.02/22.23         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 22.02/22.23      inference('simplify', [status(thm)], ['40'])).
% 22.02/22.23  thf('67', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['65', '66'])).
% 22.02/22.23  thf('68', plain,
% 22.02/22.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 22.02/22.23         (((X24) != (X23))
% 22.02/22.23          | (r2_hidden @ X24 @ X25)
% 22.02/22.23          | ((X25) != (k1_tarski @ X23)))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_tarski])).
% 22.02/22.23  thf('69', plain, (![X23 : $i]: (r2_hidden @ X23 @ (k1_tarski @ X23))),
% 22.02/22.23      inference('simplify', [status(thm)], ['68'])).
% 22.02/22.23  thf('70', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 22.02/22.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 22.02/22.23  thf('71', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['69', '70'])).
% 22.02/22.23  thf('72', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 22.02/22.23      inference('clc', [status(thm)], ['67', '71'])).
% 22.02/22.23  thf('73', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((sk_B @ X0) = (sk_B_1 @ X0))
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['64', '72'])).
% 22.02/22.23  thf('74', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 22.02/22.23      inference('simplify', [status(thm)], ['57'])).
% 22.02/22.23  thf('75', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['73', '74'])).
% 22.02/22.23  thf('76', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         ((v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 22.02/22.23      inference('simplify', [status(thm)], ['75'])).
% 22.02/22.23  thf('77', plain,
% 22.02/22.23      (![X8 : $i, X9 : $i]:
% 22.02/22.23         (((X9) = (X8))
% 22.02/22.23          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 22.02/22.23          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X9))),
% 22.02/22.23      inference('cnf', [status(esa)], [t2_tarski])).
% 22.02/22.23  thf('78', plain,
% 22.02/22.23      (![X23 : $i, X26 : $i]:
% 22.02/22.23         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 22.02/22.23      inference('simplify', [status(thm)], ['40'])).
% 22.02/22.23  thf('79', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X1)
% 22.02/22.23          | ((k1_tarski @ X0) = (X1))
% 22.02/22.23          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['77', '78'])).
% 22.02/22.23  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 22.02/22.23      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 22.02/22.23  thf('81', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((sk_C_1 @ k1_xboole_0 @ (k1_tarski @ X0)) = (X0))
% 22.02/22.23          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['79', '80'])).
% 22.02/22.23  thf('82', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['17', '18'])).
% 22.02/22.23  thf('83', plain,
% 22.02/22.23      (![X0 : $i]: ((sk_C_1 @ k1_xboole_0 @ (k1_tarski @ X0)) = (X0))),
% 22.02/22.23      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 22.02/22.23  thf('84', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (((sk_C_1 @ k1_xboole_0 @ X0) = (sk_B @ X0))
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['76', '83'])).
% 22.02/22.23  thf('85', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 22.02/22.23          | ((X0) = (k5_xboole_0 @ X1 @ X1)))),
% 22.02/22.23      inference('sup+', [status(thm)], ['9', '29'])).
% 22.02/22.23  thf('86', plain, (~ (v1_xboole_0 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('87', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 22.02/22.23          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 22.02/22.23      inference('sup-', [status(thm)], ['85', '86'])).
% 22.02/22.23  thf('88', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 22.02/22.23      inference('demod', [status(thm)], ['35', '36'])).
% 22.02/22.23  thf('89', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)),
% 22.02/22.23      inference('demod', [status(thm)], ['87', '88'])).
% 22.02/22.23  thf('90', plain,
% 22.02/22.23      (((r2_hidden @ (sk_B @ sk_A) @ sk_A)
% 22.02/22.23        | (v1_xboole_0 @ sk_A)
% 22.02/22.23        | ~ (v1_zfmisc_1 @ sk_A))),
% 22.02/22.23      inference('sup+', [status(thm)], ['84', '89'])).
% 22.02/22.23  thf('91', plain, ((v1_zfmisc_1 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('92', plain,
% 22.02/22.23      (((r2_hidden @ (sk_B @ sk_A) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('demod', [status(thm)], ['90', '91'])).
% 22.02/22.23  thf('93', plain, (~ (v1_xboole_0 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('94', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 22.02/22.23      inference('clc', [status(thm)], ['92', '93'])).
% 22.02/22.23  thf('95', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         (~ (r2_hidden @ X1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | ((X1) = (sk_B_1 @ X0)))),
% 22.02/22.23      inference('sup-', [status(thm)], ['58', '59'])).
% 22.02/22.23  thf('96', plain,
% 22.02/22.23      ((((sk_B @ sk_A) = (sk_B_1 @ sk_A))
% 22.02/22.23        | ~ (v1_zfmisc_1 @ sk_A)
% 22.02/22.23        | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('sup-', [status(thm)], ['94', '95'])).
% 22.02/22.23  thf('97', plain, ((v1_zfmisc_1 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('98', plain,
% 22.02/22.23      ((((sk_B @ sk_A) = (sk_B_1 @ sk_A)) | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('demod', [status(thm)], ['96', '97'])).
% 22.02/22.23  thf('99', plain, (~ (v1_xboole_0 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('100', plain, (((sk_B @ sk_A) = (sk_B_1 @ sk_A))),
% 22.02/22.23      inference('clc', [status(thm)], ['98', '99'])).
% 22.02/22.23  thf('101', plain,
% 22.02/22.23      ((((sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2)) = (sk_B @ sk_A))
% 22.02/22.23        | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('demod', [status(thm)], ['63', '100'])).
% 22.02/22.23  thf('102', plain, (~ (v1_xboole_0 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('103', plain,
% 22.02/22.23      (((sk_C_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_2)) = (sk_B @ sk_A))),
% 22.02/22.23      inference('clc', [status(thm)], ['101', '102'])).
% 22.02/22.23  thf('104', plain, (((sk_B @ sk_A) = (sk_B_1 @ sk_A))),
% 22.02/22.23      inference('clc', [status(thm)], ['98', '99'])).
% 22.02/22.23  thf('105', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         (~ (v1_zfmisc_1 @ X0)
% 22.02/22.23          | (v1_xboole_0 @ X0)
% 22.02/22.23          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 22.02/22.23      inference('simplify', [status(thm)], ['57'])).
% 22.02/22.23  thf('106', plain,
% 22.02/22.23      ((((sk_A) = (k1_tarski @ (sk_B @ sk_A)))
% 22.02/22.23        | (v1_xboole_0 @ sk_A)
% 22.02/22.23        | ~ (v1_zfmisc_1 @ sk_A))),
% 22.02/22.23      inference('sup+', [status(thm)], ['104', '105'])).
% 22.02/22.23  thf('107', plain, ((v1_zfmisc_1 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('108', plain,
% 22.02/22.23      ((((sk_A) = (k1_tarski @ (sk_B @ sk_A))) | (v1_xboole_0 @ sk_A))),
% 22.02/22.23      inference('demod', [status(thm)], ['106', '107'])).
% 22.02/22.23  thf('109', plain, (~ (v1_xboole_0 @ sk_A)),
% 22.02/22.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.02/22.23  thf('110', plain, (((sk_A) = (k1_tarski @ (sk_B @ sk_A)))),
% 22.02/22.23      inference('clc', [status(thm)], ['108', '109'])).
% 22.02/22.23  thf('111', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_2))),
% 22.02/22.23      inference('demod', [status(thm)], ['46', '103', '110'])).
% 22.02/22.23  thf('112', plain,
% 22.02/22.23      (![X10 : $i, X12 : $i]:
% 22.02/22.23         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 22.02/22.23          | ~ (r1_tarski @ X10 @ X12))),
% 22.02/22.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 22.02/22.23  thf('113', plain,
% 22.02/22.23      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 22.02/22.23      inference('sup-', [status(thm)], ['111', '112'])).
% 22.02/22.23  thf(t48_xboole_1, axiom,
% 22.02/22.23    (![A:$i,B:$i]:
% 22.02/22.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 22.02/22.23  thf('114', plain,
% 22.02/22.23      (![X21 : $i, X22 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 22.02/22.23           = (k3_xboole_0 @ X21 @ X22))),
% 22.02/22.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.02/22.23  thf('115', plain,
% 22.02/22.23      (![X21 : $i, X22 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 22.02/22.23           = (k3_xboole_0 @ X21 @ X22))),
% 22.02/22.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.02/22.23  thf('116', plain,
% 22.02/22.23      (![X0 : $i, X1 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 22.02/22.23           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.02/22.23      inference('sup+', [status(thm)], ['114', '115'])).
% 22.02/22.23  thf('117', plain,
% 22.02/22.23      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 22.02/22.23      inference('demod', [status(thm)], ['113', '116'])).
% 22.02/22.23  thf('118', plain,
% 22.02/22.23      (![X13 : $i, X14 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X13 @ X14)
% 22.02/22.23           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 22.02/22.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.23  thf('119', plain,
% 22.02/22.23      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_2))
% 22.02/22.23         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['117', '118'])).
% 22.02/22.23  thf('120', plain,
% 22.02/22.23      (![X21 : $i, X22 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 22.02/22.23           = (k3_xboole_0 @ X21 @ X22))),
% 22.02/22.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.02/22.23  thf(t2_boole, axiom,
% 22.02/22.23    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 22.02/22.23  thf('121', plain,
% 22.02/22.23      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 22.02/22.23      inference('cnf', [status(esa)], [t2_boole])).
% 22.02/22.23  thf('122', plain,
% 22.02/22.23      (![X13 : $i, X14 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X13 @ X14)
% 22.02/22.23           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 22.02/22.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.23  thf('123', plain,
% 22.02/22.23      (![X0 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['121', '122'])).
% 22.02/22.23  thf(t3_boole, axiom,
% 22.02/22.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 22.02/22.23  thf('124', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 22.02/22.23      inference('cnf', [status(esa)], [t3_boole])).
% 22.02/22.23  thf('125', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 22.02/22.23      inference('sup+', [status(thm)], ['123', '124'])).
% 22.02/22.23  thf('126', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_A))),
% 22.02/22.23      inference('demod', [status(thm)], ['119', '120', '125'])).
% 22.02/22.23  thf('127', plain,
% 22.02/22.23      (![X13 : $i, X14 : $i]:
% 22.02/22.23         ((k4_xboole_0 @ X13 @ X14)
% 22.02/22.23           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 22.02/22.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.02/22.23  thf('128', plain,
% 22.02/22.23      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_A))),
% 22.02/22.23      inference('sup+', [status(thm)], ['126', '127'])).
% 22.02/22.23  thf('129', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.02/22.23      inference('demod', [status(thm)], ['5', '8'])).
% 22.02/22.23  thf('130', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 22.02/22.23      inference('demod', [status(thm)], ['128', '129'])).
% 22.02/22.23  thf('131', plain,
% 22.02/22.23      (![X10 : $i, X11 : $i]:
% 22.02/22.23         ((r1_tarski @ X10 @ X11)
% 22.02/22.23          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 22.02/22.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 22.02/22.23  thf('132', plain,
% 22.02/22.23      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B_2))),
% 22.02/22.23      inference('sup-', [status(thm)], ['130', '131'])).
% 22.02/22.23  thf('133', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 22.02/22.23      inference('simplify', [status(thm)], ['132'])).
% 22.02/22.23  thf('134', plain, ($false), inference('demod', [status(thm)], ['0', '133'])).
% 22.02/22.23  
% 22.02/22.23  % SZS output end Refutation
% 22.02/22.23  
% 22.02/22.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
