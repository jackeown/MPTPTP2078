%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjdELLbl9u

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:41 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 231 expanded)
%              Number of leaves         :   28 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          : 1121 (3616 expanded)
%              Number of equality atoms :    1 (   8 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t59_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r2_hidden @ D @ B ) )
                     => ( ( C = D )
                        | ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ D ) ) ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v3_tdlat_3 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X6 ) @ X5 ) @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ X3 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v3_tex_2 @ ( sk_C_1 @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X13: $i] :
      ( ~ ( v3_tex_2 @ X13 @ sk_A )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i] :
      ( ~ ( v3_tex_2 @ X13 @ sk_A )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v3_tex_2 @ ( sk_C_1 @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v3_tex_2 @ ( sk_C_1 @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','58'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('63',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjdELLbl9u
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:02:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 60 iterations in 0.095s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.55  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.38/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.55  thf(t66_tex_2, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.38/0.55         ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ?[B:$i]:
% 0.38/0.55         ( ( v3_tex_2 @ B @ A ) & 
% 0.38/0.55           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.55            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55          ( ?[B:$i]:
% 0.38/0.55            ( ( v3_tex_2 @ B @ A ) & 
% 0.38/0.55              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.38/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(rc2_subset_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ?[B:$i]:
% 0.38/0.55       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.38/0.55  thf(t59_tex_2, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.38/0.55         ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v2_tex_2 @ B @ A ) <=>
% 0.38/0.55             ( ![C:$i]:
% 0.38/0.55               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55                 ( ![D:$i]:
% 0.38/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55                     ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) ) =>
% 0.38/0.55                       ( ( ( C ) = ( D ) ) | 
% 0.38/0.55                         ( r1_xboole_0 @
% 0.38/0.55                           ( k2_pre_topc @
% 0.38/0.55                             A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.38/0.55                           ( k2_pre_topc @
% 0.38/0.55                             A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X7 : $i, X8 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.38/0.55          | (m1_subset_1 @ (sk_D @ X7 @ X8) @ (u1_struct_0 @ X8))
% 0.38/0.55          | (v2_tex_2 @ X7 @ X8)
% 0.38/0.55          | ~ (l1_pre_topc @ X8)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X8)
% 0.38/0.55          | ~ (v2_pre_topc @ X8)
% 0.38/0.55          | (v2_struct_0 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t59_tex_2])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf(t36_tex_2, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.38/0.55          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X6) @ X5) @ X6)
% 0.38/0.55          | ~ (l1_pre_topc @ X6)
% 0.38/0.55          | ~ (v2_pre_topc @ X6)
% 0.38/0.55          | (v2_struct_0 @ X6))),
% 0.38/0.55      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ 
% 0.38/0.55             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55              (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55             X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ 
% 0.38/0.55           (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55            (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55           X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf(dt_k6_domain_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.55       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ X3)
% 0.38/0.55          | ~ (m1_subset_1 @ X4 @ X3)
% 0.38/0.55          | (m1_subset_1 @ (k6_domain_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (m1_subset_1 @ 
% 0.38/0.55             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55              (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf(t65_tex_2, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.38/0.55         ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.55                ( ![C:$i]:
% 0.38/0.55                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (v2_tex_2 @ X11 @ X12)
% 0.38/0.55          | (v3_tex_2 @ (sk_C_1 @ X11 @ X12) @ X12)
% 0.38/0.55          | ~ (l1_pre_topc @ X12)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X12)
% 0.38/0.55          | ~ (v2_pre_topc @ X12)
% 0.38/0.55          | (v2_struct_0 @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v3_tex_2 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55              X0) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | ~ (v2_tex_2 @ 
% 0.38/0.55               (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55                (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v2_tex_2 @ 
% 0.38/0.55             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55              (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v3_tex_2 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55              X0) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | (v3_tex_2 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55              X0) @ 
% 0.38/0.55             X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v3_tex_2 @ 
% 0.38/0.55           (sk_C_1 @ 
% 0.38/0.55            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55             (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55            X0) @ 
% 0.38/0.55           X0)
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ 
% 0.38/0.55           (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55            (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55           X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (m1_subset_1 @ 
% 0.38/0.55             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55              (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (v2_tex_2 @ X11 @ X12)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ X11 @ X12) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (l1_pre_topc @ X12)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X12)
% 0.38/0.55          | ~ (v2_pre_topc @ X12)
% 0.38/0.55          | (v2_struct_0 @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (m1_subset_1 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55              X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | ~ (v2_tex_2 @ 
% 0.38/0.55               (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55                (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v2_tex_2 @ 
% 0.38/0.55             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55              (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (m1_subset_1 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55              X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0)
% 0.38/0.55          | (m1_subset_1 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55              X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '19'])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((m1_subset_1 @ 
% 0.38/0.55           (sk_C_1 @ 
% 0.38/0.55            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.55             (sk_D @ (sk_B @ (u1_struct_0 @ X0)) @ X0)) @ 
% 0.38/0.55            X0) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.55          | (v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X13 : $i]:
% 0.38/0.55         (~ (v3_tex_2 @ X13 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (((v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ~ (v3_tdlat_3 @ sk_A)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | ~ (v3_tex_2 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)) @ 
% 0.38/0.55              sk_A) @ 
% 0.38/0.55             sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('25', plain, ((v3_tdlat_3 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (((v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | ~ (v3_tex_2 @ 
% 0.38/0.55             (sk_C_1 @ 
% 0.38/0.55              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55               (sk_D @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)) @ 
% 0.38/0.55              sk_A) @ 
% 0.38/0.55             sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (((v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ~ (v3_tdlat_3 @ sk_A)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['14', '27'])).
% 0.38/0.55  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('30', plain, ((v3_tdlat_3 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (((v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A))),
% 0.38/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.55  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (((v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (v2_tex_2 @ X11 @ X12)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ X11 @ X12) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (l1_pre_topc @ X12)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X12)
% 0.38/0.55          | ~ (v2_pre_topc @ X12)
% 0.38/0.55          | (v2_struct_0 @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ X0)) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | ~ (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (m1_subset_1 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ~ (v3_tdlat_3 @ sk_A)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['35', '38'])).
% 0.38/0.55  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('41', plain, ((v3_tdlat_3 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (m1_subset_1 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.38/0.55  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      (((m1_subset_1 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['43', '44'])).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      (![X13 : $i]:
% 0.38/0.55         (~ (v3_tex_2 @ X13 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | ~ (v3_tex_2 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      (((v2_tex_2 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.38/0.55  thf('50', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (v2_tex_2 @ X11 @ X12)
% 0.38/0.55          | (v3_tex_2 @ (sk_C_1 @ X11 @ X12) @ X12)
% 0.38/0.55          | ~ (l1_pre_topc @ X12)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X12)
% 0.38/0.55          | ~ (v2_pre_topc @ X12)
% 0.38/0.55          | (v2_struct_0 @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v3_tex_2 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ X0)) @ X0) @ X0)
% 0.38/0.55          | ~ (v2_tex_2 @ (sk_B @ (u1_struct_0 @ X0)) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v3_tex_2 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ sk_A)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ~ (v3_tdlat_3 @ sk_A)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '51'])).
% 0.38/0.55  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('54', plain, ((v3_tdlat_3 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.55        | (v3_tex_2 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.38/0.55  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      (((v3_tex_2 @ (sk_C_1 @ (sk_B @ (u1_struct_0 @ sk_A)) @ sk_A) @ sk_A)
% 0.38/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.55  thf('59', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['47', '58'])).
% 0.38/0.55  thf(fc2_struct_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      (![X2 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (l1_struct_0 @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.55  thf('61', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.55  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(dt_l1_pre_topc, axiom,
% 0.38/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.55  thf('63', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.55  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.55  thf('65', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)], ['61', '64'])).
% 0.38/0.55  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
