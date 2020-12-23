%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tSSy2dzELb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:04 EST 2020

% Result     : Theorem 11.57s
% Output     : Refutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 143 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  671 (1184 expanded)
%              Number of equality atoms :   47 (  66 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v2_tex_2 @ X23 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( X21 = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['44','45'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tSSy2dzELb
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:29:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 11.57/11.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.57/11.83  % Solved by: fo/fo7.sh
% 11.57/11.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.57/11.83  % done 4150 iterations in 11.369s
% 11.57/11.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.57/11.83  % SZS output start Refutation
% 11.57/11.83  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 11.57/11.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.57/11.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.57/11.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.57/11.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.57/11.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.57/11.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.57/11.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.57/11.83  thf(sk_B_type, type, sk_B: $i > $i).
% 11.57/11.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.57/11.83  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 11.57/11.83  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 11.57/11.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.57/11.83  thf(sk_A_type, type, sk_A: $i).
% 11.57/11.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.57/11.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.57/11.83  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 11.57/11.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.57/11.83  thf(sk_B_2_type, type, sk_B_2: $i).
% 11.57/11.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.57/11.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 11.57/11.83  thf(t46_tex_2, conjecture,
% 11.57/11.83    (![A:$i]:
% 11.57/11.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.57/11.83       ( ![B:$i]:
% 11.57/11.83         ( ( ( v1_xboole_0 @ B ) & 
% 11.57/11.83             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.57/11.83           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 11.57/11.83  thf(zf_stmt_0, negated_conjecture,
% 11.57/11.83    (~( ![A:$i]:
% 11.57/11.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 11.57/11.83            ( l1_pre_topc @ A ) ) =>
% 11.57/11.83          ( ![B:$i]:
% 11.57/11.83            ( ( ( v1_xboole_0 @ B ) & 
% 11.57/11.83                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.57/11.83              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 11.57/11.83    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 11.57/11.83  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 11.57/11.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.83  thf(l13_xboole_0, axiom,
% 11.57/11.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 11.57/11.83  thf('1', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.57/11.83  thf('2', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 11.57/11.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.83  thf('3', plain, ((v1_xboole_0 @ sk_B_2)),
% 11.57/11.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.83  thf('4', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.57/11.83  thf('5', plain, (((sk_B_2) = (k1_xboole_0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['3', '4'])).
% 11.57/11.83  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 11.57/11.83      inference('demod', [status(thm)], ['2', '5'])).
% 11.57/11.83  thf('7', plain,
% 11.57/11.83      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('sup+', [status(thm)], ['1', '6'])).
% 11.57/11.83  thf(t9_mcart_1, axiom,
% 11.57/11.83    (![A:$i]:
% 11.57/11.83     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 11.57/11.83          ( ![B:$i]:
% 11.57/11.83            ( ~( ( r2_hidden @ B @ A ) & 
% 11.57/11.83                 ( ![C:$i,D:$i]:
% 11.57/11.83                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 11.57/11.83                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 11.57/11.83  thf('8', plain,
% 11.57/11.83      (![X13 : $i]:
% 11.57/11.83         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 11.57/11.83      inference('cnf', [status(esa)], [t9_mcart_1])).
% 11.57/11.83  thf(t1_subset, axiom,
% 11.57/11.83    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 11.57/11.83  thf('9', plain,
% 11.57/11.83      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 11.57/11.83      inference('cnf', [status(esa)], [t1_subset])).
% 11.57/11.83  thf('10', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['8', '9'])).
% 11.57/11.83  thf(redefinition_k6_domain_1, axiom,
% 11.57/11.83    (![A:$i,B:$i]:
% 11.57/11.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 11.57/11.83       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 11.57/11.83  thf('11', plain,
% 11.57/11.83      (![X19 : $i, X20 : $i]:
% 11.57/11.83         ((v1_xboole_0 @ X19)
% 11.57/11.83          | ~ (m1_subset_1 @ X20 @ X19)
% 11.57/11.83          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 11.57/11.83      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 11.57/11.83  thf('12', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((X0) = (k1_xboole_0))
% 11.57/11.83          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 11.57/11.83          | (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['10', '11'])).
% 11.57/11.83  thf('13', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.57/11.83  thf('14', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 11.57/11.83          | ((X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('clc', [status(thm)], ['12', '13'])).
% 11.57/11.83  thf('15', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['8', '9'])).
% 11.57/11.83  thf(t36_tex_2, axiom,
% 11.57/11.83    (![A:$i]:
% 11.57/11.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.57/11.83       ( ![B:$i]:
% 11.57/11.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.57/11.83           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 11.57/11.83  thf('16', plain,
% 11.57/11.83      (![X24 : $i, X25 : $i]:
% 11.57/11.83         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 11.57/11.83          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 11.57/11.83          | ~ (l1_pre_topc @ X25)
% 11.57/11.83          | ~ (v2_pre_topc @ X25)
% 11.57/11.83          | (v2_struct_0 @ X25))),
% 11.57/11.83      inference('cnf', [status(esa)], [t36_tex_2])).
% 11.57/11.83  thf('17', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 11.57/11.83          | (v2_struct_0 @ X0)
% 11.57/11.83          | ~ (v2_pre_topc @ X0)
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | (v2_tex_2 @ 
% 11.57/11.83             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 11.57/11.83             X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['15', '16'])).
% 11.57/11.83  thf('18', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 11.57/11.83          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | ~ (v2_pre_topc @ X0)
% 11.57/11.83          | (v2_struct_0 @ X0)
% 11.57/11.83          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('sup+', [status(thm)], ['14', '17'])).
% 11.57/11.83  thf('19', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         ((v2_struct_0 @ X0)
% 11.57/11.83          | ~ (v2_pre_topc @ X0)
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 11.57/11.83          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 11.57/11.83      inference('simplify', [status(thm)], ['18'])).
% 11.57/11.83  thf('20', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 11.57/11.83          | ((X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('clc', [status(thm)], ['12', '13'])).
% 11.57/11.83  thf('21', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['8', '9'])).
% 11.57/11.83  thf(dt_k6_domain_1, axiom,
% 11.57/11.83    (![A:$i,B:$i]:
% 11.57/11.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 11.57/11.83       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 11.57/11.83  thf('22', plain,
% 11.57/11.83      (![X17 : $i, X18 : $i]:
% 11.57/11.83         ((v1_xboole_0 @ X17)
% 11.57/11.83          | ~ (m1_subset_1 @ X18 @ X17)
% 11.57/11.83          | (m1_subset_1 @ (k6_domain_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17)))),
% 11.57/11.83      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 11.57/11.83  thf('23', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((X0) = (k1_xboole_0))
% 11.57/11.83          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 11.57/11.83             (k1_zfmisc_1 @ X0))
% 11.57/11.83          | (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['21', '22'])).
% 11.57/11.83  thf('24', plain,
% 11.57/11.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.57/11.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 11.57/11.83  thf('25', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 11.57/11.83          | ((X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('clc', [status(thm)], ['23', '24'])).
% 11.57/11.83  thf('26', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 11.57/11.83          | ((X0) = (k1_xboole_0))
% 11.57/11.83          | ((X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('sup+', [status(thm)], ['20', '25'])).
% 11.57/11.83  thf('27', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((X0) = (k1_xboole_0))
% 11.57/11.83          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 11.57/11.83      inference('simplify', [status(thm)], ['26'])).
% 11.57/11.83  thf(t4_subset_1, axiom,
% 11.57/11.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 11.57/11.83  thf('28', plain,
% 11.57/11.83      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 11.57/11.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 11.57/11.83  thf(d7_tex_2, axiom,
% 11.57/11.83    (![A:$i]:
% 11.57/11.83     ( ( l1_pre_topc @ A ) =>
% 11.57/11.83       ( ![B:$i]:
% 11.57/11.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.57/11.83           ( ( v3_tex_2 @ B @ A ) <=>
% 11.57/11.83             ( ( v2_tex_2 @ B @ A ) & 
% 11.57/11.83               ( ![C:$i]:
% 11.57/11.83                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.57/11.83                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 11.57/11.83                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 11.57/11.83  thf('29', plain,
% 11.57/11.83      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.57/11.83         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 11.57/11.83          | ~ (v3_tex_2 @ X21 @ X22)
% 11.57/11.83          | ~ (v2_tex_2 @ X23 @ X22)
% 11.57/11.83          | ~ (r1_tarski @ X21 @ X23)
% 11.57/11.83          | ((X21) = (X23))
% 11.57/11.83          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 11.57/11.83          | ~ (l1_pre_topc @ X22))),
% 11.57/11.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 11.57/11.83  thf('30', plain,
% 11.57/11.83      (![X0 : $i, X1 : $i]:
% 11.57/11.83         (~ (l1_pre_topc @ X0)
% 11.57/11.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 11.57/11.83          | ((k1_xboole_0) = (X1))
% 11.57/11.83          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 11.57/11.83          | ~ (v2_tex_2 @ X1 @ X0)
% 11.57/11.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['28', '29'])).
% 11.57/11.83  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 11.57/11.83  thf('31', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 11.57/11.83      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.57/11.83  thf('32', plain,
% 11.57/11.83      (![X0 : $i, X1 : $i]:
% 11.57/11.83         (~ (l1_pre_topc @ X0)
% 11.57/11.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 11.57/11.83          | ((k1_xboole_0) = (X1))
% 11.57/11.83          | ~ (v2_tex_2 @ X1 @ X0)
% 11.57/11.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 11.57/11.83      inference('demod', [status(thm)], ['30', '31'])).
% 11.57/11.83  thf('33', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 11.57/11.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 11.57/11.83          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 11.57/11.83          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 11.57/11.83          | ~ (l1_pre_topc @ X0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['27', '32'])).
% 11.57/11.83  thf(t1_boole, axiom,
% 11.57/11.83    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.57/11.83  thf('34', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 11.57/11.83      inference('cnf', [status(esa)], [t1_boole])).
% 11.57/11.83  thf(t49_zfmisc_1, axiom,
% 11.57/11.83    (![A:$i,B:$i]:
% 11.57/11.83     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 11.57/11.83  thf('35', plain,
% 11.57/11.83      (![X3 : $i, X4 : $i]:
% 11.57/11.83         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 11.57/11.83      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 11.57/11.83  thf('36', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 11.57/11.83      inference('sup-', [status(thm)], ['34', '35'])).
% 11.57/11.83  thf('37', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 11.57/11.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 11.57/11.83          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 11.57/11.83          | ~ (l1_pre_topc @ X0))),
% 11.57/11.83      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 11.57/11.83  thf('38', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | ~ (v2_pre_topc @ X0)
% 11.57/11.83          | (v2_struct_0 @ X0)
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 11.57/11.83          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('sup-', [status(thm)], ['19', '37'])).
% 11.57/11.83  thf('39', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 11.57/11.83          | (v2_struct_0 @ X0)
% 11.57/11.83          | ~ (v2_pre_topc @ X0)
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 11.57/11.83      inference('simplify', [status(thm)], ['38'])).
% 11.57/11.83  thf('40', plain,
% 11.57/11.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.57/11.83        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 11.57/11.83        | ~ (l1_pre_topc @ sk_A)
% 11.57/11.83        | ~ (v2_pre_topc @ sk_A)
% 11.57/11.83        | (v2_struct_0 @ sk_A))),
% 11.57/11.83      inference('sup-', [status(thm)], ['7', '39'])).
% 11.57/11.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.57/11.83  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.57/11.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.57/11.83  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 11.57/11.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.83  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 11.57/11.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.83  thf('44', plain,
% 11.57/11.83      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 11.57/11.83      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 11.57/11.83  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 11.57/11.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.83  thf('46', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 11.57/11.83      inference('clc', [status(thm)], ['44', '45'])).
% 11.57/11.83  thf(rc7_pre_topc, axiom,
% 11.57/11.83    (![A:$i]:
% 11.57/11.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.57/11.83       ( ?[B:$i]:
% 11.57/11.83         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 11.57/11.83           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 11.57/11.83  thf('47', plain,
% 11.57/11.83      (![X16 : $i]:
% 11.57/11.83         ((m1_subset_1 @ (sk_B_1 @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 11.57/11.83          | ~ (l1_pre_topc @ X16)
% 11.57/11.83          | ~ (v2_pre_topc @ X16)
% 11.57/11.83          | (v2_struct_0 @ X16))),
% 11.57/11.83      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 11.57/11.83  thf(cc1_subset_1, axiom,
% 11.57/11.83    (![A:$i]:
% 11.57/11.83     ( ( v1_xboole_0 @ A ) =>
% 11.57/11.83       ( ![B:$i]:
% 11.57/11.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 11.57/11.83  thf('48', plain,
% 11.57/11.83      (![X6 : $i, X7 : $i]:
% 11.57/11.83         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 11.57/11.83          | (v1_xboole_0 @ X6)
% 11.57/11.83          | ~ (v1_xboole_0 @ X7))),
% 11.57/11.83      inference('cnf', [status(esa)], [cc1_subset_1])).
% 11.57/11.83  thf('49', plain,
% 11.57/11.83      (![X0 : $i]:
% 11.57/11.83         ((v2_struct_0 @ X0)
% 11.57/11.83          | ~ (v2_pre_topc @ X0)
% 11.57/11.83          | ~ (l1_pre_topc @ X0)
% 11.57/11.83          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 11.57/11.83          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 11.57/11.83      inference('sup-', [status(thm)], ['47', '48'])).
% 11.57/11.83  thf('50', plain,
% 11.57/11.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.57/11.83        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 11.57/11.83        | ~ (l1_pre_topc @ sk_A)
% 11.57/11.83        | ~ (v2_pre_topc @ sk_A)
% 11.57/11.84        | (v2_struct_0 @ sk_A))),
% 11.57/11.84      inference('sup-', [status(thm)], ['46', '49'])).
% 11.57/11.84  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.57/11.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.57/11.84  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 11.57/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.84  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 11.57/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.84  thf('54', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 11.57/11.84      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 11.57/11.84  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 11.57/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.84  thf('56', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 11.57/11.84      inference('clc', [status(thm)], ['54', '55'])).
% 11.57/11.84  thf('57', plain,
% 11.57/11.84      (![X16 : $i]:
% 11.57/11.84         (~ (v1_xboole_0 @ (sk_B_1 @ X16))
% 11.57/11.84          | ~ (l1_pre_topc @ X16)
% 11.57/11.84          | ~ (v2_pre_topc @ X16)
% 11.57/11.84          | (v2_struct_0 @ X16))),
% 11.57/11.84      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 11.57/11.84  thf('58', plain,
% 11.57/11.84      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 11.57/11.84      inference('sup-', [status(thm)], ['56', '57'])).
% 11.57/11.84  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 11.57/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.84  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 11.57/11.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.84  thf('61', plain, ((v2_struct_0 @ sk_A)),
% 11.57/11.84      inference('demod', [status(thm)], ['58', '59', '60'])).
% 11.57/11.84  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 11.57/11.84  
% 11.57/11.84  % SZS output end Refutation
% 11.57/11.84  
% 11.68/11.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
