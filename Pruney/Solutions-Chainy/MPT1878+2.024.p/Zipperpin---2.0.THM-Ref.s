%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mJQqp7gWMI

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:06 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 132 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  766 (1280 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
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

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
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

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mJQqp7gWMI
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 195 iterations in 0.125s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(t46_tex_2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.58            ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.39/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(l13_xboole_0, axiom,
% 0.39/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.58  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['1', '4'])).
% 0.39/0.58  thf(d1_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf(rc7_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ?[B:$i]:
% 0.39/0.58         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.58           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X14 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (sk_B_1 @ X14) @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.58          | ~ (l1_pre_topc @ X14)
% 0.39/0.58          | ~ (v2_pre_topc @ X14)
% 0.39/0.58          | (v2_struct_0 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.39/0.58  thf(t4_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X9 @ X10)
% 0.39/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.39/0.58          | (m1_subset_1 @ X9 @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.39/0.58  thf(t36_tex_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X22 : $i, X23 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.39/0.58          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.39/0.58          | ~ (l1_pre_topc @ X23)
% 0.39/0.58          | ~ (v2_pre_topc @ X23)
% 0.39/0.58          | (v2_struct_0 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v2_tex_2 @ 
% 0.39/0.58             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_tex_2 @ 
% 0.39/0.58           (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.39/0.58  thf(dt_k6_domain_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X15)
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ X15)
% 0.39/0.58          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (m1_subset_1 @ 
% 0.39/0.58             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf(t4_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.58  thf(d7_tex_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.58             ( ( v2_tex_2 @ B @ A ) & 
% 0.39/0.58               ( ![C:$i]:
% 0.39/0.58                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.58                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.39/0.58          | ~ (v3_tex_2 @ X19 @ X20)
% 0.39/0.58          | ~ (v2_tex_2 @ X21 @ X20)
% 0.39/0.58          | ~ (r1_tarski @ X19 @ X21)
% 0.39/0.58          | ((X19) = (X21))
% 0.39/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.39/0.58          | ~ (l1_pre_topc @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.58          | ((k1_xboole_0) = (X1))
% 0.39/0.58          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.39/0.58          | ~ (v2_tex_2 @ X1 @ X0)
% 0.39/0.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.58  thf('20', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.58          | ((k1_xboole_0) = (X1))
% 0.39/0.58          | ~ (v2_tex_2 @ X1 @ X0)
% 0.39/0.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | ~ (v2_tex_2 @ 
% 0.39/0.58               (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.39/0.58          | ((k1_xboole_0)
% 0.39/0.58              = (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))))
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_xboole_0)
% 0.39/0.58            = (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))))
% 0.39/0.58          | ~ (v2_tex_2 @ 
% 0.39/0.58               (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))) @ X0)
% 0.39/0.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | ((k1_xboole_0)
% 0.39/0.58              = (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_xboole_0)
% 0.39/0.58            = (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0))))
% 0.39/0.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ((k1_xboole_0)
% 0.39/0.58            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '25'])).
% 0.39/0.58  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ((k1_xboole_0)
% 0.39/0.58            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.39/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X17)
% 0.39/0.58          | ~ (m1_subset_1 @ X18 @ X17)
% 0.39/0.58          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X0)
% 0.39/0.58          | ~ (v2_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.58          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (sk_B_1 @ X0)))
% 0.39/0.58              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A))))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['29', '32'])).
% 0.39/0.58  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A))))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_A)))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.58  thf(t1_boole, axiom,
% 0.39/0.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.58  thf('38', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.58  thf(t49_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.58  thf('40', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.39/0.58  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ (sk_B_1 @ sk_A)))),
% 0.39/0.58      inference('clc', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf(fc2_struct_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X13 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.39/0.58          | ~ (l1_struct_0 @ X13)
% 0.39/0.58          | (v2_struct_0 @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_l1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.58  thf('49', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['45', '48'])).
% 0.39/0.58  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('51', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['49', '50'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (![X14 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ (sk_B_1 @ X14))
% 0.39/0.58          | ~ (l1_pre_topc @ X14)
% 0.39/0.58          | ~ (v2_pre_topc @ X14)
% 0.39/0.58          | (v2_struct_0 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.58  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('56', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.39/0.58  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
