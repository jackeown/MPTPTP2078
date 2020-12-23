%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAjO66hqXp

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 118 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   22
%              Number of atoms          :  667 ( 949 expanded)
%              Number of equality atoms :   70 (  95 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ~ ( v1_zfmisc_1 @ X30 )
      | ( X30
        = ( k6_domain_1 @ X30 @ ( sk_B @ X30 ) ) )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('3',plain,(
    ! [X30: $i] :
      ( ~ ( v1_zfmisc_1 @ X30 )
      | ( m1_subset_1 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( ( k6_domain_1 @ X28 @ X29 )
        = ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X30: $i] :
      ( ~ ( v1_zfmisc_1 @ X30 )
      | ( X30
        = ( k6_domain_1 @ X30 @ ( sk_B @ X30 ) ) )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','27'])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_tarski @ X27 )
       != ( k2_xboole_0 @ X25 @ X26 ) )
      | ( zip_tseitin_2 @ X26 @ X25 @ X27 )
      | ( zip_tseitin_1 @ X26 @ X25 @ X27 )
      | ( zip_tseitin_0 @ X26 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_tarski @ X27 )
       != ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) ) )
      | ( zip_tseitin_2 @ X26 @ X25 @ X27 )
      | ( zip_tseitin_1 @ X26 @ X25 @ X27 )
      | ( zip_tseitin_0 @ X26 @ X25 @ X27 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
       != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,
    ( ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X24
        = ( k1_tarski @ X22 ) )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X20
        = ( k1_tarski @ X21 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('41',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('46',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','46'])).

thf('48',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAjO66hqXp
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 117 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(t1_tex_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.49              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.20/0.49  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf(d1_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.49         ( ?[B:$i]:
% 0.20/0.49           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X30 : $i]:
% 0.20/0.49         (~ (v1_zfmisc_1 @ X30)
% 0.20/0.49          | ((X30) = (k6_domain_1 @ X30 @ (sk_B @ X30)))
% 0.20/0.49          | (v1_xboole_0 @ X30))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X30 : $i]:
% 0.20/0.49         (~ (v1_zfmisc_1 @ X30)
% 0.20/0.49          | (m1_subset_1 @ (sk_B @ X30) @ X30)
% 0.20/0.49          | (v1_xboole_0 @ X30))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.49  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X28)
% 0.20/0.49          | ~ (m1_subset_1 @ X29 @ X28)
% 0.20/0.49          | ((k6_domain_1 @ X28 @ X29) = (k1_tarski @ X29)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (v1_xboole_0 @ X0)
% 0.20/0.49          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X30 : $i]:
% 0.20/0.49         (~ (v1_zfmisc_1 @ X30)
% 0.20/0.49          | ((X30) = (k6_domain_1 @ X30 @ (sk_B @ X30)))
% 0.20/0.49          | (v1_xboole_0 @ X30))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.49  thf('11', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('13', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(t98_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ X7 @ X8)
% 0.20/0.49           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.49  thf(l51_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X7 @ X8))
% 0.20/0.49           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_A))
% 0.20/0.49         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('19', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X7 @ X8))
% 0.20/0.49           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X0 @ X0))
% 0.20/0.49           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.49  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('26', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.49  thf('28', plain, (((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_A)) = (sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '27'])).
% 0.20/0.49  thf(t43_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.49          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.49          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_2, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.20/0.49       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_4, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.49       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_6, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.49       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_7, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.20/0.49          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.49          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         (((k1_tarski @ X27) != (k2_xboole_0 @ X25 @ X26))
% 0.20/0.49          | (zip_tseitin_2 @ X26 @ X25 @ X27)
% 0.20/0.49          | (zip_tseitin_1 @ X26 @ X25 @ X27)
% 0.20/0.49          | (zip_tseitin_0 @ X26 @ X25 @ X27))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         (((k1_tarski @ X27) != (k3_tarski @ (k2_tarski @ X25 @ X26)))
% 0.20/0.49          | (zip_tseitin_2 @ X26 @ X25 @ X27)
% 0.20/0.49          | (zip_tseitin_1 @ X26 @ X25 @ X27)
% 0.20/0.49          | (zip_tseitin_0 @ X26 @ X25 @ X27))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) != (sk_B_1))
% 0.20/0.49          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.49          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.49          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k6_domain_1 @ X0 @ (sk_B @ X0)) != (sk_B_1))
% 0.20/0.49          | (v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.20/0.49          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.20/0.49          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (sk_B_1))
% 0.20/0.49          | (v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.20/0.49          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.20/0.49          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.20/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.49          | (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (((zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.49  thf('36', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.49      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         (((X24) = (k1_tarski @ X22)) | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         (((X20) = (k1_tarski @ X21)) | ~ (zip_tseitin_1 @ X20 @ X19 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.20/0.49        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (((X18) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X18 @ X17 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((sk_A) = (sk_B_1))
% 0.20/0.49        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.49        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '46'])).
% 0.20/0.49  thf('48', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['1', '53'])).
% 0.20/0.49  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
