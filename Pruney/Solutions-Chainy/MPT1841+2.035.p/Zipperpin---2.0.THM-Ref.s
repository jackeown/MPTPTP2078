%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.USXXTsdS4E

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:33 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 811 expanded)
%              Number of leaves         :   32 ( 256 expanded)
%              Depth                    :   24
%              Number of atoms          :  766 (6055 expanded)
%              Number of equality atoms :   56 ( 292 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X31 @ X32 ) )
      | ( r1_tarski @ X31 @ X32 )
      | ~ ( v1_zfmisc_1 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tex_2])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X23 ) @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_B_1 @ X0 ) @ X0 )
      = ( sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( sk_B_1 @ X0 ) )
      = ( sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X31 @ X32 ) )
      | ( r1_tarski @ X31 @ X32 )
      | ~ ( v1_zfmisc_1 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tex_2])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
        = sk_A )
      | ~ ( v1_zfmisc_1 @ sk_A )
      | ( ( k3_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
        = sk_A )
      | ( ( k3_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( ( k3_xboole_0 @ sk_A @ ( sk_B_1 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( sk_B_1 @ X0 ) )
      = ( sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('32',plain,
    ( ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('34',plain,
    ( ~ ( v1_subset_1 @ sk_A @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('37',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ( ( k6_domain_1 @ X29 @ X30 )
        = ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('38',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_2 ) @ sk_A )
    = ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X31 @ X32 ) )
      | ( r1_tarski @ X31 @ X32 )
      | ~ ( v1_zfmisc_1 @ X31 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_tex_2])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','70'])).

thf('72',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('74',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( sk_B_1 @ X0 ) )
      | ( X0
        = ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_A @ k1_xboole_0 )
    | ( sk_A
      = ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','71'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_A @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['66','69'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r1_tarski @ sk_A @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','82'])).

thf('84',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('87',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('92',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X21 )
      | ( v1_subset_1 @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_subset_1 @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X23: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','71'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['86','100'])).

thf('102',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['85','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['86','100'])).

thf('104',plain,(
    $false ),
    inference('sup-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.USXXTsdS4E
% 0.10/0.31  % Computer   : n007.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 09:58:21 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.31  % Number of cores: 8
% 0.16/0.32  % Python version: Python 3.6.8
% 0.16/0.32  % Running in FO mode
% 1.52/1.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.52/1.74  % Solved by: fo/fo7.sh
% 1.52/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.74  % done 2422 iterations in 1.315s
% 1.52/1.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.52/1.74  % SZS output start Refutation
% 1.52/1.74  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.52/1.74  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.52/1.74  thf(sk_B_type, type, sk_B: $i > $i).
% 1.52/1.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.52/1.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.52/1.74  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.52/1.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.52/1.74  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.52/1.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.52/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.52/1.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.52/1.74  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.52/1.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.52/1.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.52/1.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.52/1.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.52/1.74  thf(t2_tex_2, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.52/1.74           ( r1_tarski @ A @ B ) ) ) ))).
% 1.52/1.74  thf('0', plain,
% 1.52/1.74      (![X31 : $i, X32 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ (k3_xboole_0 @ X31 @ X32))
% 1.52/1.74          | (r1_tarski @ X31 @ X32)
% 1.52/1.74          | ~ (v1_zfmisc_1 @ X31)
% 1.52/1.74          | (v1_xboole_0 @ X31))),
% 1.52/1.74      inference('cnf', [status(esa)], [t2_tex_2])).
% 1.52/1.74  thf(d1_xboole_0, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.52/1.74  thf('1', plain,
% 1.52/1.74      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.52/1.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.52/1.74  thf(rc3_subset_1, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ?[B:$i]:
% 1.52/1.74       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 1.52/1.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.52/1.74  thf('2', plain,
% 1.52/1.74      (![X23 : $i]: (m1_subset_1 @ (sk_B_1 @ X23) @ (k1_zfmisc_1 @ X23))),
% 1.52/1.74      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.52/1.74  thf(t3_subset, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.52/1.74  thf('3', plain,
% 1.52/1.74      (![X24 : $i, X25 : $i]:
% 1.52/1.74         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 1.52/1.74      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.74  thf('4', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['2', '3'])).
% 1.52/1.74  thf(d3_tarski, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( r1_tarski @ A @ B ) <=>
% 1.52/1.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.52/1.74  thf('5', plain,
% 1.52/1.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.74         (~ (r2_hidden @ X5 @ X6)
% 1.52/1.74          | (r2_hidden @ X5 @ X7)
% 1.52/1.74          | ~ (r1_tarski @ X6 @ X7))),
% 1.52/1.74      inference('cnf', [status(esa)], [d3_tarski])).
% 1.52/1.74  thf('6', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['4', '5'])).
% 1.52/1.74  thf('7', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 1.52/1.74          | (r2_hidden @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['1', '6'])).
% 1.52/1.74  thf('8', plain,
% 1.52/1.74      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 1.52/1.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.52/1.74  thf('9', plain,
% 1.52/1.74      (![X0 : $i]: ((v1_xboole_0 @ (sk_B_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.74  thf(l13_xboole_0, axiom,
% 1.52/1.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.52/1.74  thf('10', plain,
% 1.52/1.74      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 1.52/1.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.52/1.74  thf('11', plain,
% 1.52/1.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['9', '10'])).
% 1.52/1.74  thf('12', plain,
% 1.52/1.74      (![X0 : $i]: ((v1_xboole_0 @ (sk_B_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.74  thf('13', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ k1_xboole_0)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0))),
% 1.52/1.74      inference('sup+', [status(thm)], ['11', '12'])).
% 1.52/1.74  thf('14', plain,
% 1.52/1.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 1.52/1.74      inference('simplify', [status(thm)], ['13'])).
% 1.52/1.74  thf('15', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ X1)
% 1.52/1.74          | ~ (v1_zfmisc_1 @ X1)
% 1.52/1.74          | (r1_tarski @ X1 @ X0)
% 1.52/1.74          | (v1_xboole_0 @ k1_xboole_0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['0', '14'])).
% 1.52/1.74  thf('16', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['2', '3'])).
% 1.52/1.74  thf(t28_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.52/1.74  thf('17', plain,
% 1.52/1.74      (![X14 : $i, X15 : $i]:
% 1.52/1.74         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.52/1.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.52/1.74  thf('18', plain,
% 1.52/1.74      (![X0 : $i]: ((k3_xboole_0 @ (sk_B_1 @ X0) @ X0) = (sk_B_1 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['16', '17'])).
% 1.52/1.74  thf(commutativity_k3_xboole_0, axiom,
% 1.52/1.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.52/1.74  thf('19', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.52/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.52/1.74  thf('20', plain,
% 1.52/1.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (sk_B_1 @ X0)) = (sk_B_1 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['18', '19'])).
% 1.52/1.74  thf('21', plain,
% 1.52/1.74      (![X31 : $i, X32 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ (k3_xboole_0 @ X31 @ X32))
% 1.52/1.74          | (r1_tarski @ X31 @ X32)
% 1.52/1.74          | ~ (v1_zfmisc_1 @ X31)
% 1.52/1.74          | (v1_xboole_0 @ X31))),
% 1.52/1.74      inference('cnf', [status(esa)], [t2_tex_2])).
% 1.52/1.74  thf('22', plain,
% 1.52/1.74      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 1.52/1.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.52/1.74  thf('23', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ X1)
% 1.52/1.74          | ~ (v1_zfmisc_1 @ X1)
% 1.52/1.74          | (r1_tarski @ X1 @ X0)
% 1.52/1.74          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['21', '22'])).
% 1.52/1.74  thf('24', plain,
% 1.52/1.74      (![X14 : $i, X15 : $i]:
% 1.52/1.74         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.52/1.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.52/1.74  thf('25', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.52/1.74          | ~ (v1_zfmisc_1 @ X1)
% 1.52/1.74          | (v1_xboole_0 @ X1)
% 1.52/1.74          | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['23', '24'])).
% 1.52/1.74  thf(t6_tex_2, conjecture,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( m1_subset_1 @ B @ A ) =>
% 1.52/1.74           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 1.52/1.74                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 1.52/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.74    (~( ![A:$i]:
% 1.52/1.74        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.52/1.74          ( ![B:$i]:
% 1.52/1.74            ( ( m1_subset_1 @ B @ A ) =>
% 1.52/1.74              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 1.52/1.74                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 1.52/1.74    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 1.52/1.74  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('27', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((k3_xboole_0 @ sk_A @ X0) = (sk_A))
% 1.52/1.74          | ~ (v1_zfmisc_1 @ sk_A)
% 1.52/1.74          | ((k3_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['25', '26'])).
% 1.52/1.74  thf('28', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('29', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (((k3_xboole_0 @ sk_A @ X0) = (sk_A))
% 1.52/1.74          | ((k3_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 1.52/1.74      inference('demod', [status(thm)], ['27', '28'])).
% 1.52/1.74  thf('30', plain,
% 1.52/1.74      ((((sk_B_1 @ sk_A) = (sk_A))
% 1.52/1.74        | ((k3_xboole_0 @ sk_A @ (sk_B_1 @ sk_A)) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup+', [status(thm)], ['20', '29'])).
% 1.52/1.74  thf('31', plain,
% 1.52/1.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (sk_B_1 @ X0)) = (sk_B_1 @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['18', '19'])).
% 1.52/1.74  thf('32', plain,
% 1.52/1.74      ((((sk_B_1 @ sk_A) = (sk_A)) | ((sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 1.52/1.74      inference('demod', [status(thm)], ['30', '31'])).
% 1.52/1.74  thf('33', plain, (![X23 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X23) @ X23)),
% 1.52/1.74      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.52/1.74  thf('34', plain,
% 1.52/1.74      ((~ (v1_subset_1 @ sk_A @ sk_A) | ((sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['32', '33'])).
% 1.52/1.74  thf('35', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('36', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(redefinition_k6_domain_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.52/1.74       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.52/1.74  thf('37', plain,
% 1.52/1.74      (![X29 : $i, X30 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ X29)
% 1.52/1.74          | ~ (m1_subset_1 @ X30 @ X29)
% 1.52/1.74          | ((k6_domain_1 @ X29 @ X30) = (k1_tarski @ X30)))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.52/1.74  thf('38', plain,
% 1.52/1.74      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 1.52/1.74        | (v1_xboole_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['36', '37'])).
% 1.52/1.74  thf('39', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('40', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 1.52/1.74      inference('clc', [status(thm)], ['38', '39'])).
% 1.52/1.74  thf('41', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 1.52/1.74      inference('demod', [status(thm)], ['35', '40'])).
% 1.52/1.74  thf('42', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(dt_k6_domain_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.52/1.74       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.52/1.74  thf('43', plain,
% 1.52/1.74      (![X27 : $i, X28 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ X27)
% 1.52/1.74          | ~ (m1_subset_1 @ X28 @ X27)
% 1.52/1.74          | (m1_subset_1 @ (k6_domain_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27)))),
% 1.52/1.74      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.52/1.74  thf('44', plain,
% 1.52/1.74      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 1.52/1.74        | (v1_xboole_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['42', '43'])).
% 1.52/1.74  thf('45', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 1.52/1.74      inference('clc', [status(thm)], ['38', '39'])).
% 1.52/1.74  thf('46', plain,
% 1.52/1.74      (((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 1.52/1.74        | (v1_xboole_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['44', '45'])).
% 1.52/1.74  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('48', plain,
% 1.52/1.74      ((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 1.52/1.74      inference('clc', [status(thm)], ['46', '47'])).
% 1.52/1.74  thf('49', plain,
% 1.52/1.74      (![X24 : $i, X25 : $i]:
% 1.52/1.74         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 1.52/1.74      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.74  thf('50', plain, ((r1_tarski @ (k1_tarski @ sk_B_2) @ sk_A)),
% 1.52/1.74      inference('sup-', [status(thm)], ['48', '49'])).
% 1.52/1.74  thf('51', plain,
% 1.52/1.74      (![X14 : $i, X15 : $i]:
% 1.52/1.74         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.52/1.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.52/1.74  thf('52', plain,
% 1.52/1.74      (((k3_xboole_0 @ (k1_tarski @ sk_B_2) @ sk_A) = (k1_tarski @ sk_B_2))),
% 1.52/1.74      inference('sup-', [status(thm)], ['50', '51'])).
% 1.52/1.74  thf('53', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.52/1.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.52/1.74  thf('54', plain,
% 1.52/1.74      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_2)) = (k1_tarski @ sk_B_2))),
% 1.52/1.74      inference('demod', [status(thm)], ['52', '53'])).
% 1.52/1.74  thf('55', plain,
% 1.52/1.74      (![X31 : $i, X32 : $i]:
% 1.52/1.74         ((v1_xboole_0 @ (k3_xboole_0 @ X31 @ X32))
% 1.52/1.74          | (r1_tarski @ X31 @ X32)
% 1.52/1.74          | ~ (v1_zfmisc_1 @ X31)
% 1.52/1.74          | (v1_xboole_0 @ X31))),
% 1.52/1.74      inference('cnf', [status(esa)], [t2_tex_2])).
% 1.52/1.74  thf('56', plain,
% 1.52/1.74      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 1.52/1.74        | (v1_xboole_0 @ sk_A)
% 1.52/1.74        | ~ (v1_zfmisc_1 @ sk_A)
% 1.52/1.74        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_2)))),
% 1.52/1.74      inference('sup+', [status(thm)], ['54', '55'])).
% 1.52/1.74  thf('57', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('58', plain,
% 1.52/1.74      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 1.52/1.74        | (v1_xboole_0 @ sk_A)
% 1.52/1.74        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_2)))),
% 1.52/1.74      inference('demod', [status(thm)], ['56', '57'])).
% 1.52/1.74  thf('59', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('60', plain,
% 1.52/1.74      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B_2))
% 1.52/1.74        | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 1.52/1.74      inference('clc', [status(thm)], ['58', '59'])).
% 1.52/1.74  thf('61', plain, ((r1_tarski @ (k1_tarski @ sk_B_2) @ sk_A)),
% 1.52/1.74      inference('sup-', [status(thm)], ['48', '49'])).
% 1.52/1.74  thf(d10_xboole_0, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.52/1.74  thf('62', plain,
% 1.52/1.74      (![X10 : $i, X12 : $i]:
% 1.52/1.74         (((X10) = (X12))
% 1.52/1.74          | ~ (r1_tarski @ X12 @ X10)
% 1.52/1.74          | ~ (r1_tarski @ X10 @ X12))),
% 1.52/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.74  thf('63', plain,
% 1.52/1.74      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_2))
% 1.52/1.74        | ((sk_A) = (k1_tarski @ sk_B_2)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['61', '62'])).
% 1.52/1.74  thf('64', plain,
% 1.52/1.74      (((v1_xboole_0 @ (k1_tarski @ sk_B_2)) | ((sk_A) = (k1_tarski @ sk_B_2)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['60', '63'])).
% 1.52/1.74  thf('65', plain,
% 1.52/1.74      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 1.52/1.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.52/1.74  thf('66', plain,
% 1.52/1.74      ((((sk_A) = (k1_tarski @ sk_B_2))
% 1.52/1.74        | ((k1_tarski @ sk_B_2) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['64', '65'])).
% 1.52/1.74  thf(t1_boole, axiom,
% 1.52/1.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.52/1.74  thf('67', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.52/1.74      inference('cnf', [status(esa)], [t1_boole])).
% 1.52/1.74  thf(t49_zfmisc_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.52/1.74  thf('68', plain,
% 1.52/1.74      (![X19 : $i, X20 : $i]:
% 1.52/1.74         ((k2_xboole_0 @ (k1_tarski @ X19) @ X20) != (k1_xboole_0))),
% 1.52/1.74      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.52/1.74  thf('69', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['67', '68'])).
% 1.52/1.74  thf('70', plain, (((sk_A) = (k1_tarski @ sk_B_2))),
% 1.52/1.74      inference('simplify_reflect-', [status(thm)], ['66', '69'])).
% 1.52/1.74  thf('71', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 1.52/1.74      inference('demod', [status(thm)], ['41', '70'])).
% 1.52/1.74  thf('72', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 1.52/1.74      inference('demod', [status(thm)], ['34', '71'])).
% 1.52/1.74  thf('73', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['2', '3'])).
% 1.52/1.74  thf('74', plain,
% 1.52/1.74      (![X10 : $i, X12 : $i]:
% 1.52/1.74         (((X10) = (X12))
% 1.52/1.74          | ~ (r1_tarski @ X12 @ X10)
% 1.52/1.74          | ~ (r1_tarski @ X10 @ X12))),
% 1.52/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.74  thf('75', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X0 @ (sk_B_1 @ X0)) | ((X0) = (sk_B_1 @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['73', '74'])).
% 1.52/1.74  thf('76', plain,
% 1.52/1.74      ((~ (r1_tarski @ sk_A @ k1_xboole_0) | ((sk_A) = (sk_B_1 @ sk_A)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['72', '75'])).
% 1.52/1.74  thf('77', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 1.52/1.74      inference('demod', [status(thm)], ['34', '71'])).
% 1.52/1.74  thf('78', plain,
% 1.52/1.74      ((~ (r1_tarski @ sk_A @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 1.52/1.74      inference('demod', [status(thm)], ['76', '77'])).
% 1.52/1.74  thf('79', plain, (((sk_A) = (k1_tarski @ sk_B_2))),
% 1.52/1.74      inference('simplify_reflect-', [status(thm)], ['66', '69'])).
% 1.52/1.74  thf('80', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['67', '68'])).
% 1.52/1.74  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['79', '80'])).
% 1.52/1.74  thf('82', plain, (~ (r1_tarski @ sk_A @ k1_xboole_0)),
% 1.52/1.74      inference('simplify_reflect-', [status(thm)], ['78', '81'])).
% 1.52/1.74  thf('83', plain,
% 1.52/1.74      (((v1_xboole_0 @ k1_xboole_0)
% 1.52/1.74        | ~ (v1_zfmisc_1 @ sk_A)
% 1.52/1.74        | (v1_xboole_0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['15', '82'])).
% 1.52/1.74  thf('84', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('85', plain, (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['83', '84'])).
% 1.52/1.74  thf('86', plain,
% 1.52/1.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 1.52/1.74      inference('simplify', [status(thm)], ['13'])).
% 1.52/1.74  thf('87', plain,
% 1.52/1.74      (![X6 : $i, X8 : $i]:
% 1.52/1.74         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 1.52/1.74      inference('cnf', [status(esa)], [d3_tarski])).
% 1.52/1.74  thf('88', plain,
% 1.52/1.74      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 1.52/1.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.52/1.74  thf('89', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['87', '88'])).
% 1.52/1.74  thf('90', plain,
% 1.52/1.74      (![X24 : $i, X26 : $i]:
% 1.52/1.74         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 1.52/1.74      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.74  thf('91', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['89', '90'])).
% 1.52/1.74  thf(cc2_subset_1, axiom,
% 1.52/1.74    (![A:$i]:
% 1.52/1.74     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.52/1.74       ( ![B:$i]:
% 1.52/1.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.52/1.74           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 1.52/1.74  thf('92', plain,
% 1.52/1.74      (![X21 : $i, X22 : $i]:
% 1.52/1.74         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 1.52/1.74          | ~ (v1_xboole_0 @ X21)
% 1.52/1.74          | (v1_subset_1 @ X21 @ X22)
% 1.52/1.74          | (v1_xboole_0 @ X22))),
% 1.52/1.74      inference('cnf', [status(esa)], [cc2_subset_1])).
% 1.52/1.74  thf('93', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (v1_xboole_0 @ X1)
% 1.52/1.74          | (v1_xboole_0 @ X0)
% 1.52/1.74          | (v1_subset_1 @ X1 @ X0)
% 1.52/1.74          | ~ (v1_xboole_0 @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['91', '92'])).
% 1.52/1.74  thf('94', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((v1_subset_1 @ X1 @ X0) | (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.52/1.74      inference('simplify', [status(thm)], ['93'])).
% 1.52/1.74  thf('95', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('96', plain,
% 1.52/1.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_subset_1 @ X0 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['94', '95'])).
% 1.52/1.74  thf('97', plain, (![X23 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X23) @ X23)),
% 1.52/1.74      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.52/1.74  thf('98', plain, (~ (v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 1.52/1.74      inference('sup-', [status(thm)], ['96', '97'])).
% 1.52/1.74  thf('99', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 1.52/1.74      inference('demod', [status(thm)], ['34', '71'])).
% 1.52/1.74  thf('100', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.74      inference('demod', [status(thm)], ['98', '99'])).
% 1.52/1.74  thf('101', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['86', '100'])).
% 1.52/1.74  thf('102', plain, ((v1_xboole_0 @ sk_A)),
% 1.52/1.74      inference('clc', [status(thm)], ['85', '101'])).
% 1.52/1.74  thf('103', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['86', '100'])).
% 1.52/1.74  thf('104', plain, ($false), inference('sup-', [status(thm)], ['102', '103'])).
% 1.52/1.74  
% 1.52/1.74  % SZS output end Refutation
% 1.52/1.74  
% 1.52/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
