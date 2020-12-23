%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YtYAVJ2m6W

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:07 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 161 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   26
%              Number of atoms          :  887 (1619 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
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
    inference('sup+',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_tex_2 @ X18 @ X19 )
      | ~ ( v2_tex_2 @ X20 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( X18 = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
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
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
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
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
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
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('48',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','63'])).

thf('65',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YtYAVJ2m6W
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.93/3.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.93/3.12  % Solved by: fo/fo7.sh
% 2.93/3.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.93/3.12  % done 2003 iterations in 2.668s
% 2.93/3.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.93/3.12  % SZS output start Refutation
% 2.93/3.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.93/3.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.93/3.12  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.93/3.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.93/3.12  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.93/3.12  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.93/3.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.93/3.12  thf(sk_B_type, type, sk_B: $i > $i).
% 2.93/3.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.93/3.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.93/3.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.93/3.12  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.93/3.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.93/3.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.93/3.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.93/3.12  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.93/3.12  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 2.93/3.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.93/3.12  thf(sk_A_type, type, sk_A: $i).
% 2.93/3.12  thf(t46_tex_2, conjecture,
% 2.93/3.12    (![A:$i]:
% 2.93/3.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.93/3.12       ( ![B:$i]:
% 2.93/3.12         ( ( ( v1_xboole_0 @ B ) & 
% 2.93/3.12             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.93/3.12           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.93/3.12  thf(zf_stmt_0, negated_conjecture,
% 2.93/3.12    (~( ![A:$i]:
% 2.93/3.12        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.93/3.12            ( l1_pre_topc @ A ) ) =>
% 2.93/3.12          ( ![B:$i]:
% 2.93/3.12            ( ( ( v1_xboole_0 @ B ) & 
% 2.93/3.12                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.93/3.12              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 2.93/3.12    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 2.93/3.12  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.12  thf(d1_xboole_0, axiom,
% 2.93/3.12    (![A:$i]:
% 2.93/3.12     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.93/3.12  thf('1', plain,
% 2.93/3.12      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.93/3.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.93/3.12  thf('2', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 2.93/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.12  thf('3', plain, ((v1_xboole_0 @ sk_B_2)),
% 2.93/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.12  thf(l13_xboole_0, axiom,
% 2.93/3.12    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.93/3.12  thf('4', plain,
% 2.93/3.12      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.93/3.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.93/3.12  thf('5', plain, (((sk_B_2) = (k1_xboole_0))),
% 2.93/3.12      inference('sup-', [status(thm)], ['3', '4'])).
% 2.93/3.12  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 2.93/3.12      inference('demod', [status(thm)], ['2', '5'])).
% 2.93/3.12  thf('7', plain,
% 2.93/3.12      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.93/3.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.93/3.12  thf(rc7_pre_topc, axiom,
% 2.93/3.12    (![A:$i]:
% 2.93/3.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.93/3.12       ( ?[B:$i]:
% 2.93/3.12         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.93/3.12           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.93/3.12  thf('8', plain,
% 2.93/3.12      (![X13 : $i]:
% 2.93/3.12         ((m1_subset_1 @ (sk_B_1 @ X13) @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.93/3.12          | ~ (l1_pre_topc @ X13)
% 2.93/3.12          | ~ (v2_pre_topc @ X13)
% 2.93/3.12          | (v2_struct_0 @ X13))),
% 2.93/3.12      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 2.93/3.12  thf(t4_subset, axiom,
% 2.93/3.12    (![A:$i,B:$i,C:$i]:
% 2.93/3.12     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.93/3.12       ( m1_subset_1 @ A @ C ) ))).
% 2.93/3.12  thf('9', plain,
% 2.93/3.12      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.93/3.12         (~ (r2_hidden @ X7 @ X8)
% 2.93/3.12          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 2.93/3.12          | (m1_subset_1 @ X7 @ X9))),
% 2.93/3.12      inference('cnf', [status(esa)], [t4_subset])).
% 2.93/3.12  thf('10', plain,
% 2.93/3.12      (![X0 : $i, X1 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.93/3.12          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 2.93/3.12      inference('sup-', [status(thm)], ['8', '9'])).
% 2.93/3.12  thf('11', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0))),
% 2.93/3.12      inference('sup-', [status(thm)], ['7', '10'])).
% 2.93/3.12  thf(redefinition_k6_domain_1, axiom,
% 2.93/3.12    (![A:$i,B:$i]:
% 2.93/3.12     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 2.93/3.12       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 2.93/3.12  thf('12', plain,
% 2.93/3.12      (![X16 : $i, X17 : $i]:
% 2.93/3.12         ((v1_xboole_0 @ X16)
% 2.93/3.12          | ~ (m1_subset_1 @ X17 @ X16)
% 2.93/3.12          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 2.93/3.12      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 2.93/3.12  thf('13', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 2.93/3.12              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.93/3.12      inference('sup-', [status(thm)], ['11', '12'])).
% 2.93/3.12  thf('14', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0))),
% 2.93/3.12      inference('sup-', [status(thm)], ['7', '10'])).
% 2.93/3.12  thf(t36_tex_2, axiom,
% 2.93/3.12    (![A:$i]:
% 2.93/3.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.93/3.12       ( ![B:$i]:
% 2.93/3.12         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.93/3.12           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 2.93/3.12  thf('15', plain,
% 2.93/3.12      (![X21 : $i, X22 : $i]:
% 2.93/3.12         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.93/3.12          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 2.93/3.12          | ~ (l1_pre_topc @ X22)
% 2.93/3.12          | ~ (v2_pre_topc @ X22)
% 2.93/3.12          | (v2_struct_0 @ X22))),
% 2.93/3.12      inference('cnf', [status(esa)], [t36_tex_2])).
% 2.93/3.12  thf('16', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v2_tex_2 @ 
% 2.93/3.12             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 2.93/3.12      inference('sup-', [status(thm)], ['14', '15'])).
% 2.93/3.12  thf('17', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_tex_2 @ 
% 2.93/3.12           (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0))),
% 2.93/3.12      inference('simplify', [status(thm)], ['16'])).
% 2.93/3.12  thf('18', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 2.93/3.12      inference('sup+', [status(thm)], ['13', '17'])).
% 2.93/3.12  thf('19', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.12          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 2.93/3.12      inference('simplify', [status(thm)], ['18'])).
% 2.93/3.12  thf('20', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 2.93/3.12              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.93/3.12      inference('sup-', [status(thm)], ['11', '12'])).
% 2.93/3.12  thf('21', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0))),
% 2.93/3.12      inference('sup-', [status(thm)], ['7', '10'])).
% 2.93/3.12  thf(dt_k6_domain_1, axiom,
% 2.93/3.12    (![A:$i,B:$i]:
% 2.93/3.12     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 2.93/3.12       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.93/3.12  thf('22', plain,
% 2.93/3.12      (![X14 : $i, X15 : $i]:
% 2.93/3.12         ((v1_xboole_0 @ X14)
% 2.93/3.12          | ~ (m1_subset_1 @ X15 @ X14)
% 2.93/3.12          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 2.93/3.12      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 2.93/3.12  thf('23', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (m1_subset_1 @ 
% 2.93/3.12             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ 
% 2.93/3.12             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.93/3.12      inference('sup-', [status(thm)], ['21', '22'])).
% 2.93/3.12  thf('24', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 2.93/3.12           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | (v2_struct_0 @ X0))),
% 2.93/3.12      inference('sup+', [status(thm)], ['20', '23'])).
% 2.93/3.12  thf('25', plain,
% 2.93/3.12      (![X0 : $i]:
% 2.93/3.12         ((v2_struct_0 @ X0)
% 2.93/3.12          | ~ (v2_pre_topc @ X0)
% 2.93/3.12          | ~ (l1_pre_topc @ X0)
% 2.93/3.12          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.12          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.12          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 2.93/3.12             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.93/3.12      inference('simplify', [status(thm)], ['24'])).
% 2.93/3.12  thf(t4_subset_1, axiom,
% 2.93/3.12    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.93/3.12  thf('26', plain,
% 2.93/3.12      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 2.93/3.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.93/3.13  thf(d7_tex_2, axiom,
% 2.93/3.13    (![A:$i]:
% 2.93/3.13     ( ( l1_pre_topc @ A ) =>
% 2.93/3.13       ( ![B:$i]:
% 2.93/3.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.13           ( ( v3_tex_2 @ B @ A ) <=>
% 2.93/3.13             ( ( v2_tex_2 @ B @ A ) & 
% 2.93/3.13               ( ![C:$i]:
% 2.93/3.13                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.93/3.13                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.93/3.13                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 2.93/3.13  thf('27', plain,
% 2.93/3.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.93/3.13         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.93/3.13          | ~ (v3_tex_2 @ X18 @ X19)
% 2.93/3.13          | ~ (v2_tex_2 @ X20 @ X19)
% 2.93/3.13          | ~ (r1_tarski @ X18 @ X20)
% 2.93/3.13          | ((X18) = (X20))
% 2.93/3.13          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.93/3.13          | ~ (l1_pre_topc @ X19))),
% 2.93/3.13      inference('cnf', [status(esa)], [d7_tex_2])).
% 2.93/3.13  thf('28', plain,
% 2.93/3.13      (![X0 : $i, X1 : $i]:
% 2.93/3.13         (~ (l1_pre_topc @ X0)
% 2.93/3.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.93/3.13          | ((k1_xboole_0) = (X1))
% 2.93/3.13          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 2.93/3.13          | ~ (v2_tex_2 @ X1 @ X0)
% 2.93/3.13          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 2.93/3.13      inference('sup-', [status(thm)], ['26', '27'])).
% 2.93/3.13  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.93/3.13  thf('29', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.93/3.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.93/3.13  thf('30', plain,
% 2.93/3.13      (![X0 : $i, X1 : $i]:
% 2.93/3.13         (~ (l1_pre_topc @ X0)
% 2.93/3.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.93/3.13          | ((k1_xboole_0) = (X1))
% 2.93/3.13          | ~ (v2_tex_2 @ X1 @ X0)
% 2.93/3.13          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 2.93/3.13      inference('demod', [status(thm)], ['28', '29'])).
% 2.93/3.13  thf('31', plain,
% 2.93/3.13      (![X0 : $i]:
% 2.93/3.13         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.13          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.13          | ~ (l1_pre_topc @ X0)
% 2.93/3.13          | ~ (v2_pre_topc @ X0)
% 2.93/3.13          | (v2_struct_0 @ X0)
% 2.93/3.13          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.93/3.13          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 2.93/3.13          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 2.93/3.13          | ~ (l1_pre_topc @ X0))),
% 2.93/3.13      inference('sup-', [status(thm)], ['25', '30'])).
% 2.93/3.13  thf('32', plain,
% 2.93/3.13      (![X0 : $i]:
% 2.93/3.13         (((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 2.93/3.13          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 2.93/3.13          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.93/3.13          | (v2_struct_0 @ X0)
% 2.93/3.13          | ~ (v2_pre_topc @ X0)
% 2.93/3.13          | ~ (l1_pre_topc @ X0)
% 2.93/3.13          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.13          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.93/3.13      inference('simplify', [status(thm)], ['31'])).
% 2.93/3.13  thf('33', plain,
% 2.93/3.13      (![X0 : $i]:
% 2.93/3.13         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.13          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.13          | ~ (l1_pre_topc @ X0)
% 2.93/3.13          | ~ (v2_pre_topc @ X0)
% 2.93/3.13          | (v2_struct_0 @ X0)
% 2.93/3.13          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.13          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.13          | ~ (l1_pre_topc @ X0)
% 2.93/3.13          | ~ (v2_pre_topc @ X0)
% 2.93/3.13          | (v2_struct_0 @ X0)
% 2.93/3.13          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.93/3.13          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0)))))),
% 2.93/3.13      inference('sup-', [status(thm)], ['19', '32'])).
% 2.93/3.13  thf('34', plain,
% 2.93/3.13      (![X0 : $i]:
% 2.93/3.13         (((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 2.93/3.13          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.93/3.13          | (v2_struct_0 @ X0)
% 2.93/3.13          | ~ (v2_pre_topc @ X0)
% 2.93/3.13          | ~ (l1_pre_topc @ X0)
% 2.93/3.13          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 2.93/3.13          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.93/3.13      inference('simplify', [status(thm)], ['33'])).
% 2.93/3.13  thf('35', plain,
% 2.93/3.13      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.13        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 2.93/3.13        | ~ (l1_pre_topc @ sk_A)
% 2.93/3.13        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.13        | (v2_struct_0 @ sk_A)
% 2.93/3.13        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 2.93/3.13      inference('sup-', [status(thm)], ['6', '34'])).
% 2.93/3.13  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('38', plain,
% 2.93/3.13      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.93/3.13        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 2.93/3.13        | (v2_struct_0 @ sk_A)
% 2.93/3.13        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 2.93/3.13      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.93/3.13  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 2.93/3.13  thf('39', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 2.93/3.13      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 2.93/3.13  thf('40', plain,
% 2.93/3.13      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.93/3.13        | (v2_struct_0 @ sk_A)
% 2.93/3.13        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 2.93/3.13        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.13      inference('sup-', [status(thm)], ['38', '39'])).
% 2.93/3.13  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.93/3.13  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.13  thf('42', plain,
% 2.93/3.13      (((v2_struct_0 @ sk_A)
% 2.93/3.13        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 2.93/3.13        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.93/3.13      inference('demod', [status(thm)], ['40', '41'])).
% 2.93/3.13  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('44', plain,
% 2.93/3.13      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ (sk_B_1 @ sk_A)))),
% 2.93/3.13      inference('clc', [status(thm)], ['42', '43'])).
% 2.93/3.13  thf('45', plain,
% 2.93/3.13      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.93/3.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.93/3.13  thf('46', plain,
% 2.93/3.13      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 2.93/3.13        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 2.93/3.13      inference('sup-', [status(thm)], ['44', '45'])).
% 2.93/3.13  thf('47', plain,
% 2.93/3.13      (![X13 : $i]:
% 2.93/3.13         (~ (v1_xboole_0 @ (sk_B_1 @ X13))
% 2.93/3.13          | ~ (l1_pre_topc @ X13)
% 2.93/3.13          | ~ (v2_pre_topc @ X13)
% 2.93/3.13          | (v2_struct_0 @ X13))),
% 2.93/3.13      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 2.93/3.13  thf('48', plain,
% 2.93/3.13      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 2.93/3.13        | (v2_struct_0 @ sk_A)
% 2.93/3.13        | ~ (v2_pre_topc @ sk_A)
% 2.93/3.13        | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.13      inference('sup-', [status(thm)], ['46', '47'])).
% 2.93/3.13  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('51', plain,
% 2.93/3.13      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 2.93/3.13      inference('demod', [status(thm)], ['48', '49', '50'])).
% 2.93/3.13  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('53', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 2.93/3.13      inference('clc', [status(thm)], ['51', '52'])).
% 2.93/3.13  thf('54', plain,
% 2.93/3.13      (![X13 : $i]:
% 2.93/3.13         ((m1_subset_1 @ (sk_B_1 @ X13) @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.93/3.13          | ~ (l1_pre_topc @ X13)
% 2.93/3.13          | ~ (v2_pre_topc @ X13)
% 2.93/3.13          | (v2_struct_0 @ X13))),
% 2.93/3.13      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 2.93/3.13  thf(t5_subset, axiom,
% 2.93/3.13    (![A:$i,B:$i,C:$i]:
% 2.93/3.13     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.93/3.13          ( v1_xboole_0 @ C ) ) ))).
% 2.93/3.13  thf('55', plain,
% 2.93/3.13      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.93/3.13         (~ (r2_hidden @ X10 @ X11)
% 2.93/3.13          | ~ (v1_xboole_0 @ X12)
% 2.93/3.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.93/3.13      inference('cnf', [status(esa)], [t5_subset])).
% 2.93/3.13  thf('56', plain,
% 2.93/3.13      (![X0 : $i, X1 : $i]:
% 2.93/3.13         ((v2_struct_0 @ X0)
% 2.93/3.13          | ~ (v2_pre_topc @ X0)
% 2.93/3.13          | ~ (l1_pre_topc @ X0)
% 2.93/3.13          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.93/3.13          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 2.93/3.13      inference('sup-', [status(thm)], ['54', '55'])).
% 2.93/3.13  thf('57', plain,
% 2.93/3.13      (![X0 : $i]:
% 2.93/3.13         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.93/3.13          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 2.93/3.13          | ~ (l1_pre_topc @ sk_A)
% 2.93/3.13          | ~ (v2_pre_topc @ sk_A)
% 2.93/3.13          | (v2_struct_0 @ sk_A))),
% 2.93/3.13      inference('sup-', [status(thm)], ['53', '56'])).
% 2.93/3.13  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.13  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('61', plain,
% 2.93/3.13      (![X0 : $i]:
% 2.93/3.13         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 2.93/3.13      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 2.93/3.13  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('63', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 2.93/3.13      inference('clc', [status(thm)], ['61', '62'])).
% 2.93/3.13  thf('64', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 2.93/3.13      inference('sup-', [status(thm)], ['1', '63'])).
% 2.93/3.13  thf('65', plain,
% 2.93/3.13      (![X13 : $i]:
% 2.93/3.13         (~ (v1_xboole_0 @ (sk_B_1 @ X13))
% 2.93/3.13          | ~ (l1_pre_topc @ X13)
% 2.93/3.13          | ~ (v2_pre_topc @ X13)
% 2.93/3.13          | (v2_struct_0 @ X13))),
% 2.93/3.13      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 2.93/3.13  thf('66', plain,
% 2.93/3.13      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 2.93/3.13      inference('sup-', [status(thm)], ['64', '65'])).
% 2.93/3.13  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 2.93/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.13  thf('69', plain, ((v2_struct_0 @ sk_A)),
% 2.93/3.13      inference('demod', [status(thm)], ['66', '67', '68'])).
% 2.93/3.13  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 2.93/3.13  
% 2.93/3.13  % SZS output end Refutation
% 2.93/3.13  
% 2.93/3.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
