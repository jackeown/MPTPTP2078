%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lNWkQkqn1C

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:32 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 221 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  831 (4285 expanded)
%              Number of equality atoms :    9 (  89 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t58_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
             => ( v2_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_tdlat_3 @ X14 )
      | ~ ( v4_pre_topc @ X15 @ X14 )
      | ( v3_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('35',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X19 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X19 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X19 ) )
      | ~ ( r2_hidden @ X19 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X18 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ ( sk_C @ X16 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('41',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lNWkQkqn1C
% 0.14/0.37  % Computer   : n021.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:23:20 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 272 iterations in 0.212s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.69  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.51/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.69  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.51/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.51/0.69  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.51/0.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.51/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.51/0.69  thf(t58_tex_2, conjecture,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.51/0.69         ( l1_pre_topc @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69           ( ( ![C:$i]:
% 0.51/0.69               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69                 ( ( r2_hidden @ C @ B ) =>
% 0.51/0.69                   ( ( k9_subset_1 @
% 0.51/0.69                       ( u1_struct_0 @ A ) @ B @ 
% 0.51/0.69                       ( k2_pre_topc @
% 0.51/0.69                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.51/0.69                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.51/0.69             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i]:
% 0.51/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.69            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.69          ( ![B:$i]:
% 0.51/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69              ( ( ![C:$i]:
% 0.51/0.69                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69                    ( ( r2_hidden @ C @ B ) =>
% 0.51/0.69                      ( ( k9_subset_1 @
% 0.51/0.69                          ( u1_struct_0 @ A ) @ B @ 
% 0.51/0.69                          ( k2_pre_topc @
% 0.51/0.69                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.51/0.69                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.51/0.69                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.51/0.69  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(t37_tex_2, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69           ( ( ![C:$i]:
% 0.51/0.69               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.51/0.69                      ( ![D:$i]:
% 0.51/0.69                        ( ( m1_subset_1 @
% 0.51/0.69                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.51/0.69                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.51/0.69                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.51/0.69             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X16 : $i, X17 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.69          | (v2_tex_2 @ X16 @ X17)
% 0.51/0.69          | (r2_hidden @ (sk_C @ X16 @ X17) @ X16)
% 0.51/0.69          | ~ (l1_pre_topc @ X17)
% 0.51/0.69          | ~ (v2_pre_topc @ X17)
% 0.51/0.69          | (v2_struct_0 @ X17))),
% 0.51/0.69      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      (((v2_struct_0 @ sk_A)
% 0.51/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.69        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.69  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (((v2_struct_0 @ sk_A)
% 0.51/0.69        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.51/0.69  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('8', plain,
% 0.51/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.69        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('clc', [status(thm)], ['6', '7'])).
% 0.51/0.69  thf('9', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('10', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.51/0.69      inference('clc', [status(thm)], ['8', '9'])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(t4_subset, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.51/0.69       ( m1_subset_1 @ A @ C ) ))).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.51/0.69          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.51/0.69          | (m1_subset_1 @ X3 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [t4_subset])).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.69          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['10', '13'])).
% 0.51/0.69  thf(dt_k6_domain_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.69       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.69  thf('15', plain,
% 0.51/0.70      (![X10 : $i, X11 : $i]:
% 0.51/0.70         ((v1_xboole_0 @ X10)
% 0.51/0.70          | ~ (m1_subset_1 @ X11 @ X10)
% 0.51/0.70          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (((m1_subset_1 @ 
% 0.51/0.70         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.51/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.70  thf(dt_k2_pre_topc, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( l1_pre_topc @ A ) & 
% 0.51/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.70       ( m1_subset_1 @
% 0.51/0.70         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (![X6 : $i, X7 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X6)
% 0.51/0.70          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.51/0.70          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (m1_subset_1 @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.70  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (m1_subset_1 @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.51/0.70  thf(t24_tdlat_3, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.70       ( ( v3_tdlat_3 @ A ) <=>
% 0.51/0.70         ( ![B:$i]:
% 0.51/0.70           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (![X14 : $i, X15 : $i]:
% 0.51/0.70         (~ (v3_tdlat_3 @ X14)
% 0.51/0.70          | ~ (v4_pre_topc @ X15 @ X14)
% 0.51/0.70          | (v3_pre_topc @ X15 @ X14)
% 0.51/0.70          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.51/0.70          | ~ (l1_pre_topc @ X14)
% 0.51/0.70          | ~ (v2_pre_topc @ X14))),
% 0.51/0.70      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.70        | (v3_pre_topc @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           sk_A)
% 0.51/0.70        | ~ (v4_pre_topc @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             sk_A)
% 0.51/0.70        | ~ (v3_tdlat_3 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.70  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('25', plain, ((v3_tdlat_3 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v3_pre_topc @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           sk_A)
% 0.51/0.70        | ~ (v4_pre_topc @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      (((m1_subset_1 @ 
% 0.51/0.70         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.51/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.70  thf(fc1_tops_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.51/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.70       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X12)
% 0.51/0.70          | ~ (v2_pre_topc @ X12)
% 0.51/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.51/0.70          | (v4_pre_topc @ (k2_pre_topc @ X12 @ X13) @ X12))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v4_pre_topc @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           sk_A)
% 0.51/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.70  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v4_pre_topc @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      (((v3_pre_topc @ 
% 0.51/0.70         (k2_pre_topc @ sk_A @ 
% 0.51/0.70          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70         sk_A)
% 0.51/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('clc', [status(thm)], ['26', '32'])).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (m1_subset_1 @ 
% 0.51/0.70           (k2_pre_topc @ sk_A @ 
% 0.51/0.70            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.51/0.70  thf('35', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.51/0.70      inference('clc', [status(thm)], ['8', '9'])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (![X19 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X19 @ sk_B_1)
% 0.51/0.70          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.70              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X19)))
% 0.51/0.70              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X19))
% 0.51/0.70          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.70  thf('38', plain,
% 0.51/0.70      (![X19 : $i]:
% 0.51/0.70         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.70            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X19)))
% 0.51/0.70            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X19))
% 0.51/0.70          | ~ (r2_hidden @ X19 @ sk_B_1))),
% 0.51/0.70      inference('clc', [status(thm)], ['36', '37'])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.51/0.70         (k2_pre_topc @ sk_A @ 
% 0.51/0.70          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.51/0.70         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['35', '38'])).
% 0.51/0.70  thf('40', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | (v2_tex_2 @ X16 @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.51/0.70          | ~ (v3_pre_topc @ X18 @ X17)
% 0.51/0.70          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X18)
% 0.51/0.70              != (k6_domain_1 @ (u1_struct_0 @ X17) @ (sk_C @ X16 @ X17)))
% 0.51/0.70          | ~ (l1_pre_topc @ X17)
% 0.51/0.70          | ~ (v2_pre_topc @ X17)
% 0.51/0.70          | (v2_struct_0 @ X17))),
% 0.51/0.70      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.51/0.70          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.70        | ~ (v3_pre_topc @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             sk_A)
% 0.51/0.70        | ~ (m1_subset_1 @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.70        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.51/0.70  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('45', plain,
% 0.51/0.70      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.51/0.70          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (v3_pre_topc @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             sk_A)
% 0.51/0.70        | ~ (m1_subset_1 @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.70        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.51/0.70  thf('46', plain,
% 0.51/0.70      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ~ (m1_subset_1 @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.70        | ~ (v3_pre_topc @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (v3_pre_topc @ 
% 0.51/0.70             (k2_pre_topc @ sk_A @ 
% 0.51/0.70              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.51/0.70             sk_A)
% 0.51/0.70        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['34', '46'])).
% 0.51/0.70  thf('48', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['33', '47'])).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A)
% 0.51/0.70        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.51/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('simplify', [status(thm)], ['48'])).
% 0.51/0.70  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('51', plain,
% 0.51/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['49', '50'])).
% 0.51/0.70  thf('52', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('53', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['51', '52'])).
% 0.51/0.70  thf(fc2_struct_0, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.70       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X9 : $i]:
% 0.51/0.70         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.51/0.70          | ~ (l1_struct_0 @ X9)
% 0.51/0.70          | (v2_struct_0 @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.51/0.70  thf('55', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.70  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(dt_l1_pre_topc, axiom,
% 0.51/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.51/0.70  thf('57', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.70  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.51/0.70  thf('59', plain, ((v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['55', '58'])).
% 0.51/0.70  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
