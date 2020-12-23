%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sY05cwIWef

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:07 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 170 expanded)
%              Number of leaves         :   34 (  65 expanded)
%              Depth                    :   25
%              Number of atoms          :  887 (1693 expanded)
%              Number of equality atoms :   24 (  29 expanded)
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

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X22 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( X20 = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','65'])).

thf('67',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sY05cwIWef
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 348 iterations in 0.230s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.52/0.70  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.70  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.52/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.70  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.52/0.70  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.52/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.70  thf(t46_tex_2, conjecture,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( ( v1_xboole_0 @ B ) & 
% 0.52/0.70             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.70           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i]:
% 0.52/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.52/0.70            ( l1_pre_topc @ A ) ) =>
% 0.52/0.70          ( ![B:$i]:
% 0.52/0.70            ( ( ( v1_xboole_0 @ B ) & 
% 0.52/0.70                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.70              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.52/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(d1_xboole_0, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.52/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.70  thf('2', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('3', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(l13_xboole_0, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('5', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.70  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.52/0.70      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.52/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.70  thf(rc7_pre_topc, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.70       ( ?[B:$i]:
% 0.52/0.70         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.52/0.70           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.52/0.70  thf('8', plain,
% 0.52/0.70      (![X15 : $i]:
% 0.52/0.70         ((m1_subset_1 @ (sk_B_1 @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.52/0.70          | ~ (l1_pre_topc @ X15)
% 0.52/0.70          | ~ (v2_pre_topc @ X15)
% 0.52/0.70          | (v2_struct_0 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.52/0.70  thf(t4_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.52/0.70       ( m1_subset_1 @ A @ C ) ))).
% 0.52/0.70  thf('9', plain,
% 0.52/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X9 @ X10)
% 0.52/0.70          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.52/0.70          | (m1_subset_1 @ X9 @ X11))),
% 0.52/0.70      inference('cnf', [status(esa)], [t4_subset])).
% 0.52/0.70  thf('10', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.52/0.70          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '10'])).
% 0.52/0.70  thf(redefinition_k6_domain_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.52/0.70       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      (![X18 : $i, X19 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X18)
% 0.52/0.70          | ~ (m1_subset_1 @ X19 @ X18)
% 0.52/0.70          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 0.52/0.70              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '10'])).
% 0.52/0.70  thf(t36_tex_2, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.70           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X23 : $i, X24 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.52/0.70          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.52/0.70          | ~ (l1_pre_topc @ X24)
% 0.52/0.70          | ~ (v2_pre_topc @ X24)
% 0.52/0.70          | (v2_struct_0 @ X24))),
% 0.52/0.70      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v2_tex_2 @ 
% 0.52/0.70             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_tex_2 @ 
% 0.52/0.70           (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['16'])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['13', '17'])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 0.52/0.70              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.70  thf('21', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['7', '10'])).
% 0.52/0.70  thf(dt_k6_domain_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.52/0.70       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      (![X16 : $i, X17 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X16)
% 0.52/0.70          | ~ (m1_subset_1 @ X17 @ X16)
% 0.52/0.70          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.52/0.70  thf('23', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (m1_subset_1 @ 
% 0.52/0.70             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.52/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.52/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['20', '23'])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.52/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['24'])).
% 0.52/0.70  thf(t4_subset_1, axiom,
% 0.52/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.52/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.70  thf(d7_tex_2, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( l1_pre_topc @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.70           ( ( v3_tex_2 @ B @ A ) <=>
% 0.52/0.70             ( ( v2_tex_2 @ B @ A ) & 
% 0.52/0.70               ( ![C:$i]:
% 0.52/0.70                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.70                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.52/0.70                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.52/0.70          | ~ (v3_tex_2 @ X20 @ X21)
% 0.52/0.70          | ~ (v2_tex_2 @ X22 @ X21)
% 0.52/0.70          | ~ (r1_tarski @ X20 @ X22)
% 0.52/0.70          | ((X20) = (X22))
% 0.52/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.52/0.70          | ~ (l1_pre_topc @ X21))),
% 0.52/0.70      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.52/0.70          | ((k1_xboole_0) = (X1))
% 0.52/0.70          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.52/0.70          | ~ (v2_tex_2 @ X1 @ X0)
% 0.52/0.70          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.70  thf('29', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.70  thf('30', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.52/0.70          | ((k1_xboole_0) = (X1))
% 0.52/0.70          | ~ (v2_tex_2 @ X1 @ X0)
% 0.52/0.70          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.52/0.70  thf('31', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.52/0.70          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.52/0.70          | ~ (l1_pre_topc @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['25', '30'])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.52/0.70          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.52/0.70          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.70  thf(t1_boole, axiom,
% 0.52/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.70  thf('33', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.52/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.52/0.70  thf(t49_zfmisc_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      (![X6 : $i, X7 : $i]:
% 0.52/0.70         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.52/0.70  thf('35', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('36', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.52/0.70          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.52/0.70  thf('37', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['19', '36'])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.52/0.70          | (v2_struct_0 @ X0)
% 0.52/0.70          | ~ (v2_pre_topc @ X0)
% 0.52/0.70          | ~ (l1_pre_topc @ X0)
% 0.52/0.70          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.52/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.52/0.70        | (v2_struct_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['6', '38'])).
% 0.52/0.70  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.52/0.70        | (v2_struct_0 @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.52/0.70  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.70      inference('clc', [status(thm)], ['42', '43'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.52/0.70        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      (![X15 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ (sk_B_1 @ X15))
% 0.52/0.70          | ~ (l1_pre_topc @ X15)
% 0.52/0.70          | ~ (v2_pre_topc @ X15)
% 0.52/0.70          | (v2_struct_0 @ X15))),
% 0.52/0.70      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.52/0.70  thf('48', plain,
% 0.52/0.70      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.52/0.70        | (v2_struct_0 @ sk_A)
% 0.52/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.52/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.70  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.52/0.71  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('53', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.52/0.71      inference('clc', [status(thm)], ['51', '52'])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      (![X15 : $i]:
% 0.52/0.71         ((m1_subset_1 @ (sk_B_1 @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.52/0.71          | ~ (l1_pre_topc @ X15)
% 0.52/0.71          | ~ (v2_pre_topc @ X15)
% 0.52/0.71          | (v2_struct_0 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.52/0.71  thf(t5_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.52/0.71          ( v1_xboole_0 @ C ) ) ))).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X12 @ X13)
% 0.52/0.71          | ~ (v1_xboole_0 @ X14)
% 0.52/0.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t5_subset])).
% 0.52/0.71  thf('56', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((v2_struct_0 @ X0)
% 0.52/0.71          | ~ (v2_pre_topc @ X0)
% 0.52/0.71          | ~ (l1_pre_topc @ X0)
% 0.52/0.71          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.52/0.71          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.52/0.71          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.52/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71          | ~ (v2_pre_topc @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['53', '56'])).
% 0.52/0.71  thf('58', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('59', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.71  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['57', '60', '61', '62'])).
% 0.52/0.71  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('65', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.52/0.71      inference('clc', [status(thm)], ['63', '64'])).
% 0.52/0.71  thf('66', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '65'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X15 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ (sk_B_1 @ X15))
% 0.52/0.71          | ~ (l1_pre_topc @ X15)
% 0.52/0.71          | ~ (v2_pre_topc @ X15)
% 0.52/0.71          | (v2_struct_0 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.71  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('71', plain, ((v2_struct_0 @ sk_A)),
% 0.52/0.71      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.52/0.71  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
