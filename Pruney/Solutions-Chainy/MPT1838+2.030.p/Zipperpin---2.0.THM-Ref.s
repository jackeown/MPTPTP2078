%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Df1itt6oBi

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 177 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   23
%              Number of atoms          :  606 (1383 expanded)
%              Number of equality atoms :   56 ( 121 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X11 @ X10 ) )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( X25
        = ( k6_domain_1 @ X25 @ ( sk_B_1 @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('6',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( m1_subset_1 @ ( sk_B_1 @ X25 ) @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X11 @ X10 ) )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X0
        = ( k1_tarski @ ( k3_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('33',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X1
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( ( sk_B @ sk_A )
      = ( k3_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( sk_B @ sk_A )
      = ( k3_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B @ sk_A )
    = ( k3_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ ( k3_tarski @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['43','49'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['23','52'])).

thf('54',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['55','56'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ k1_xboole_0 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    sk_A = sk_B_2 ),
    inference('sup+',[status(thm)],['4','66'])).

thf('68',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Df1itt6oBi
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 216 iterations in 0.135s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(t1_tex_2, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.57           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.57              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.20/0.57  thf('0', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t12_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.57  thf(l51_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i]:
% 0.20/0.57         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         (((k3_tarski @ (k2_tarski @ X11 @ X10)) = (X10))
% 0.20/0.57          | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf('4', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)) = (sk_B_2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.57  thf(d1_tex_2, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.57         ( ?[B:$i]:
% 0.20/0.57           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X25 : $i]:
% 0.20/0.57         (~ (v1_zfmisc_1 @ X25)
% 0.20/0.57          | ((X25) = (k6_domain_1 @ X25 @ (sk_B_1 @ X25)))
% 0.20/0.57          | (v1_xboole_0 @ X25))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X25 : $i]:
% 0.20/0.57         (~ (v1_zfmisc_1 @ X25)
% 0.20/0.57          | (m1_subset_1 @ (sk_B_1 @ X25) @ X25)
% 0.20/0.57          | (v1_xboole_0 @ X25))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.57  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.57       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X23 : $i, X24 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X23)
% 0.20/0.57          | ~ (m1_subset_1 @ X24 @ X23)
% 0.20/0.57          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.20/0.57          | (v1_xboole_0 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['5', '9'])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.57  thf(t69_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf(d3_tarski, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X4 : $i, X6 : $i]:
% 0.20/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X4 : $i, X6 : $i]:
% 0.20/0.57         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X10 : $i, X11 : $i]:
% 0.20/0.57         (((k3_tarski @ (k2_tarski @ X11 @ X10)) = (X10))
% 0.20/0.57          | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf('18', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.57  thf('19', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['12', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k3_tarski @ X0) = (sk_B_1 @ X0))
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['11', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((X0) = (k1_tarski @ (k3_tarski @ X0)))
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | ((X0) = (k1_tarski @ (k3_tarski @ X0))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.57  thf(d1_xboole_0, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.57  thf('25', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.57          | (r2_hidden @ X3 @ X5)
% 0.20/0.57          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.57  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('30', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 0.20/0.57      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | ((X0) = (k1_tarski @ (k3_tarski @ X0))))),
% 0.20/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.57  thf(d1_tarski, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.57          | ((X18) = (X15))
% 0.20/0.57          | ((X17) != (k1_tarski @ X15)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X15 : $i, X18 : $i]:
% 0.20/0.57         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.57          | (v1_xboole_0 @ X0)
% 0.20/0.57          | ((X1) = (k3_tarski @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['31', '33'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      ((((sk_B @ sk_A) = (k3_tarski @ sk_B_2))
% 0.20/0.57        | (v1_xboole_0 @ sk_B_2)
% 0.20/0.57        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['30', '34'])).
% 0.20/0.57  thf('36', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      ((((sk_B @ sk_A) = (k3_tarski @ sk_B_2)) | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('38', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('39', plain, (((sk_B @ sk_A) = (k3_tarski @ sk_B_2))),
% 0.20/0.57      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (((r2_hidden @ (k3_tarski @ sk_B_2) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.57  thf('42', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('43', plain, ((r2_hidden @ (k3_tarski @ sk_B_2) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X4 : $i, X6 : $i]:
% 0.20/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (![X15 : $i, X18 : $i]:
% 0.20/0.57         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.57          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X4 : $i, X6 : $i]:
% 0.20/0.57         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.57          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.57          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.57  thf('50', plain, ((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_2)) @ sk_A)),
% 0.20/0.57      inference('sup-', [status(thm)], ['43', '49'])).
% 0.20/0.57  thf(l32_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X7 : $i, X9 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B_2)) @ sk_A)
% 0.20/0.57         = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      ((((k4_xboole_0 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.20/0.57        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.20/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.57      inference('sup+', [status(thm)], ['23', '52'])).
% 0.20/0.57  thf('54', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      ((((k4_xboole_0 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.20/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.57  thf('56', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('57', plain, (((k4_xboole_0 @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.20/0.57      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.57  thf(t39_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i]:
% 0.20/0.57         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.20/0.57           = (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i]:
% 0.20/0.57         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i]:
% 0.20/0.57         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i]:
% 0.20/0.57         ((k3_tarski @ (k2_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))
% 0.20/0.57           = (k3_tarski @ (k2_tarski @ X13 @ X14)))),
% 0.20/0.57      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (((k3_tarski @ (k2_tarski @ sk_A @ k1_xboole_0))
% 0.20/0.57         = (k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['57', '61'])).
% 0.20/0.57  thf(t1_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.57  thf('63', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i]:
% 0.20/0.57         ((k3_tarski @ (k2_tarski @ X21 @ X22)) = (k2_xboole_0 @ X21 @ X22))),
% 0.20/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      (![X12 : $i]: ((k3_tarski @ (k2_tarski @ X12 @ k1_xboole_0)) = (X12))),
% 0.20/0.57      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.57  thf('66', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)))),
% 0.20/0.57      inference('demod', [status(thm)], ['62', '65'])).
% 0.20/0.57  thf('67', plain, (((sk_A) = (sk_B_2))),
% 0.20/0.57      inference('sup+', [status(thm)], ['4', '66'])).
% 0.20/0.57  thf('68', plain, (((sk_A) != (sk_B_2))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('69', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
