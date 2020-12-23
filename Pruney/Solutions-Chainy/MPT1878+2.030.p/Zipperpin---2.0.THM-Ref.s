%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NwvqPheZFq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:07 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 147 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   21
%              Number of atoms          :  871 (1489 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('1',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X22 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( X20 = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NwvqPheZFq
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.87/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.07  % Solved by: fo/fo7.sh
% 0.87/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.07  % done 705 iterations in 0.624s
% 0.87/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.07  % SZS output start Refutation
% 0.87/1.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.87/1.07  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.87/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.07  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.87/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.87/1.07  thf(sk_B_type, type, sk_B: $i > $i).
% 0.87/1.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.87/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.87/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.87/1.07  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.87/1.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.87/1.07  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.87/1.07  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.87/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.87/1.07  thf(t46_tex_2, conjecture,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( ( v1_xboole_0 @ B ) & 
% 0.87/1.07             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.87/1.07           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.87/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.07    (~( ![A:$i]:
% 0.87/1.07        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.87/1.07            ( l1_pre_topc @ A ) ) =>
% 0.87/1.07          ( ![B:$i]:
% 0.87/1.07            ( ( ( v1_xboole_0 @ B ) & 
% 0.87/1.07                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.87/1.07              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.87/1.07    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.87/1.07  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(l13_xboole_0, axiom,
% 0.87/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.87/1.07  thf('3', plain,
% 0.87/1.07      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.07  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.87/1.07      inference('demod', [status(thm)], ['1', '4'])).
% 0.87/1.07  thf(d1_xboole_0, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.87/1.07  thf('6', plain,
% 0.87/1.07      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.87/1.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.87/1.07  thf(rc7_pre_topc, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.07       ( ?[B:$i]:
% 0.87/1.07         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.87/1.07           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.87/1.07  thf('7', plain,
% 0.87/1.07      (![X15 : $i]:
% 0.87/1.07         ((m1_subset_1 @ (sk_B_1 @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.87/1.07          | ~ (l1_pre_topc @ X15)
% 0.87/1.07          | ~ (v2_pre_topc @ X15)
% 0.87/1.07          | (v2_struct_0 @ X15))),
% 0.87/1.07      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.87/1.07  thf(t4_subset, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.87/1.07       ( m1_subset_1 @ A @ C ) ))).
% 0.87/1.07  thf('8', plain,
% 0.87/1.07      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X12 @ X13)
% 0.87/1.07          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.87/1.07          | (m1_subset_1 @ X12 @ X14))),
% 0.87/1.07      inference('cnf', [status(esa)], [t4_subset])).
% 0.87/1.07  thf('9', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.87/1.07          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['7', '8'])).
% 0.87/1.07  thf('10', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['6', '9'])).
% 0.87/1.07  thf(redefinition_k6_domain_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.87/1.07       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.87/1.07  thf('11', plain,
% 0.87/1.07      (![X18 : $i, X19 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ X18)
% 0.87/1.07          | ~ (m1_subset_1 @ X19 @ X18)
% 0.87/1.07          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.87/1.07      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.87/1.07  thf('12', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 0.87/1.07              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['10', '11'])).
% 0.87/1.07  thf('13', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['6', '9'])).
% 0.87/1.07  thf(t36_tex_2, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.87/1.07           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.87/1.07  thf('14', plain,
% 0.87/1.07      (![X23 : $i, X24 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.87/1.07          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.87/1.07          | ~ (l1_pre_topc @ X24)
% 0.87/1.07          | ~ (v2_pre_topc @ X24)
% 0.87/1.07          | (v2_struct_0 @ X24))),
% 0.87/1.07      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.87/1.07  thf('15', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v2_tex_2 @ 
% 0.87/1.07             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['13', '14'])).
% 0.87/1.07  thf('16', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_tex_2 @ 
% 0.87/1.07           (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0))),
% 0.87/1.07      inference('simplify', [status(thm)], ['15'])).
% 0.87/1.07  thf('17', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['12', '16'])).
% 0.87/1.07  thf('18', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 0.87/1.07      inference('simplify', [status(thm)], ['17'])).
% 0.87/1.07  thf('19', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 0.87/1.07              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['10', '11'])).
% 0.87/1.07  thf('20', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['6', '9'])).
% 0.87/1.07  thf(dt_k6_domain_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.87/1.07       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.87/1.07  thf('21', plain,
% 0.87/1.07      (![X16 : $i, X17 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ X16)
% 0.87/1.07          | ~ (m1_subset_1 @ X17 @ X16)
% 0.87/1.07          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.87/1.07      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.87/1.07  thf('22', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (m1_subset_1 @ 
% 0.87/1.07             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.87/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['20', '21'])).
% 0.87/1.07  thf('23', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.87/1.07           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['19', '22'])).
% 0.87/1.07  thf('24', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.87/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.87/1.07      inference('simplify', [status(thm)], ['23'])).
% 0.87/1.07  thf(t4_subset_1, axiom,
% 0.87/1.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.87/1.07  thf('25', plain,
% 0.87/1.07      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.87/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.87/1.07  thf(d7_tex_2, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( l1_pre_topc @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07           ( ( v3_tex_2 @ B @ A ) <=>
% 0.87/1.07             ( ( v2_tex_2 @ B @ A ) & 
% 0.87/1.07               ( ![C:$i]:
% 0.87/1.07                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.87/1.07                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.87/1.07  thf('26', plain,
% 0.87/1.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.87/1.07          | ~ (v3_tex_2 @ X20 @ X21)
% 0.87/1.07          | ~ (v2_tex_2 @ X22 @ X21)
% 0.87/1.07          | ~ (r1_tarski @ X20 @ X22)
% 0.87/1.07          | ((X20) = (X22))
% 0.87/1.07          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.87/1.07          | ~ (l1_pre_topc @ X21))),
% 0.87/1.07      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.87/1.07  thf('27', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.87/1.07          | ((k1_xboole_0) = (X1))
% 0.87/1.07          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.87/1.07          | ~ (v2_tex_2 @ X1 @ X0)
% 0.87/1.07          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['25', '26'])).
% 0.87/1.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.87/1.07  thf('28', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.87/1.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.07  thf('29', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.87/1.07          | ((k1_xboole_0) = (X1))
% 0.87/1.07          | ~ (v2_tex_2 @ X1 @ X0)
% 0.87/1.07          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.87/1.07      inference('demod', [status(thm)], ['27', '28'])).
% 0.87/1.07  thf('30', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.87/1.07          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.87/1.07          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.87/1.07          | ~ (l1_pre_topc @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['24', '29'])).
% 0.87/1.07  thf('31', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.87/1.07          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.87/1.07          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['30'])).
% 0.87/1.07  thf(t1_boole, axiom,
% 0.87/1.07    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.87/1.07  thf('32', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.87/1.07      inference('cnf', [status(esa)], [t1_boole])).
% 0.87/1.07  thf(t49_zfmisc_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.87/1.07  thf('33', plain,
% 0.87/1.07      (![X6 : $i, X7 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.87/1.07      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.87/1.07  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.87/1.07  thf('35', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.87/1.07          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.87/1.07  thf('36', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['18', '35'])).
% 0.87/1.07  thf('37', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['36'])).
% 0.87/1.07  thf('38', plain,
% 0.87/1.07      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.87/1.07        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.87/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.87/1.07        | ~ (v2_pre_topc @ sk_A)
% 0.87/1.07        | (v2_struct_0 @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['5', '37'])).
% 0.87/1.07  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('41', plain,
% 0.87/1.07      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.87/1.07        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.87/1.07        | (v2_struct_0 @ sk_A))),
% 0.87/1.07      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.87/1.07  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('43', plain,
% 0.87/1.07      (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('clc', [status(thm)], ['41', '42'])).
% 0.87/1.07  thf('44', plain,
% 0.87/1.07      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.87/1.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.87/1.07  thf('45', plain,
% 0.87/1.07      (![X15 : $i]:
% 0.87/1.07         ((m1_subset_1 @ (sk_B_1 @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.87/1.07          | ~ (l1_pre_topc @ X15)
% 0.87/1.07          | ~ (v2_pre_topc @ X15)
% 0.87/1.07          | (v2_struct_0 @ X15))),
% 0.87/1.07      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.87/1.07  thf(l3_subset_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.87/1.07  thf('46', plain,
% 0.87/1.07      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.87/1.07         (~ (r2_hidden @ X8 @ X9)
% 0.87/1.07          | (r2_hidden @ X8 @ X10)
% 0.87/1.07          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.87/1.07      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.87/1.07  thf('47', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.87/1.07          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['45', '46'])).
% 0.87/1.07  thf('48', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | (r2_hidden @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | (v2_struct_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['44', '47'])).
% 0.87/1.07  thf('49', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.87/1.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.87/1.07  thf('50', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v2_struct_0 @ X0)
% 0.87/1.07          | ~ (v2_pre_topc @ X0)
% 0.87/1.07          | ~ (l1_pre_topc @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.87/1.07          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['48', '49'])).
% 0.87/1.07  thf('51', plain,
% 0.87/1.07      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.87/1.07        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.87/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.87/1.07        | ~ (v2_pre_topc @ sk_A)
% 0.87/1.07        | (v2_struct_0 @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['43', '50'])).
% 0.87/1.07  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('54', plain,
% 0.87/1.07      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.87/1.07        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.87/1.07        | (v2_struct_0 @ sk_A))),
% 0.87/1.07      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.87/1.07  thf('55', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (sk_B_1 @ sk_A)))),
% 0.87/1.07      inference('simplify', [status(thm)], ['54'])).
% 0.87/1.07  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('57', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.87/1.07      inference('clc', [status(thm)], ['55', '56'])).
% 0.87/1.07  thf('58', plain,
% 0.87/1.07      (![X15 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ (sk_B_1 @ X15))
% 0.87/1.07          | ~ (l1_pre_topc @ X15)
% 0.87/1.07          | ~ (v2_pre_topc @ X15)
% 0.87/1.07          | (v2_struct_0 @ X15))),
% 0.87/1.07      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.87/1.07  thf('59', plain,
% 0.87/1.07      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['57', '58'])).
% 0.87/1.07  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.87/1.07      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.87/1.07  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.87/1.07  
% 0.87/1.07  % SZS output end Refutation
% 0.87/1.07  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
