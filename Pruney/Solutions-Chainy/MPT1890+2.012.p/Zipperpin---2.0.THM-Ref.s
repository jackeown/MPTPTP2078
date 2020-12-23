%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UVtEkKju0s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:32 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 229 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  871 (4761 expanded)
%              Number of equality atoms :    9 ( 101 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_tdlat_3 @ X9 )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('43',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('44',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X14 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('47',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ X13 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ ( sk_C @ X11 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','61'])).

thf('63',plain,(
    $false ),
    inference('sup-',[status(thm)],['9','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UVtEkKju0s
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:52:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 119 iterations in 0.118s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.60  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.43/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.60  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.43/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.43/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.43/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.43/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(t58_tex_2, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.43/0.61         ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( ![C:$i]:
% 0.43/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                 ( ( r2_hidden @ C @ B ) =>
% 0.43/0.61                   ( ( k9_subset_1 @
% 0.43/0.61                       ( u1_struct_0 @ A ) @ B @ 
% 0.43/0.61                       ( k2_pre_topc @
% 0.43/0.61                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.43/0.61                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.43/0.61             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61              ( ( ![C:$i]:
% 0.43/0.61                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                    ( ( r2_hidden @ C @ B ) =>
% 0.43/0.61                      ( ( k9_subset_1 @
% 0.43/0.61                          ( u1_struct_0 @ A ) @ B @ 
% 0.43/0.61                          ( k2_pre_topc @
% 0.43/0.61                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.43/0.61                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.43/0.61                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t37_tex_2, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( ![C:$i]:
% 0.43/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.43/0.61                      ( ![D:$i]:
% 0.43/0.61                        ( ( m1_subset_1 @
% 0.43/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.43/0.61                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.43/0.61                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.43/0.61             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (v2_tex_2 @ X11 @ X12)
% 0.43/0.61          | (r2_hidden @ (sk_C @ X11 @ X12) @ X11)
% 0.43/0.61          | ~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.43/0.61  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.43/0.61      inference('clc', [status(thm)], ['5', '6'])).
% 0.43/0.61  thf('8', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('9', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.43/0.61      inference('clc', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t5_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.43/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.61          | ~ (v1_xboole_0 @ X2)
% 0.43/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (v2_tex_2 @ X11 @ X12)
% 0.43/0.61          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ (u1_struct_0 @ X12))
% 0.43/0.61          | ~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.61  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.61  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf('21', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf(dt_k6_domain_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.43/0.61       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X5 : $i, X6 : $i]:
% 0.43/0.61         ((v1_xboole_0 @ X5)
% 0.43/0.61          | ~ (m1_subset_1 @ X6 @ X5)
% 0.43/0.61          | (m1_subset_1 @ (k6_domain_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (((m1_subset_1 @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.43/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf(dt_k2_pre_topc, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61       ( m1_subset_1 @
% 0.43/0.61         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X3)
% 0.43/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.43/0.61          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (m1_subset_1 @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (m1_subset_1 @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf(t24_tdlat_3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ( v3_tdlat_3 @ A ) <=>
% 0.43/0.61         ( ![B:$i]:
% 0.43/0.61           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (~ (v3_tdlat_3 @ X9)
% 0.43/0.61          | ~ (v4_pre_topc @ X10 @ X9)
% 0.43/0.61          | (v3_pre_topc @ X10 @ X9)
% 0.43/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.43/0.61          | ~ (l1_pre_topc @ X9)
% 0.43/0.61          | ~ (v2_pre_topc @ X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (v3_pre_topc @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           sk_A)
% 0.43/0.61        | ~ (v4_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | ~ (v3_tdlat_3 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('33', plain, ((v3_tdlat_3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v3_pre_topc @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           sk_A)
% 0.43/0.61        | ~ (v4_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (((m1_subset_1 @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.43/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf(fc1_tops_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X7 : $i, X8 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X7)
% 0.43/0.61          | ~ (v2_pre_topc @ X7)
% 0.43/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.43/0.61          | (v4_pre_topc @ (k2_pre_topc @ X7 @ X8) @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v4_pre_topc @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.61  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v4_pre_topc @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (((v3_pre_topc @ 
% 0.43/0.61         (k2_pre_topc @ sk_A @ 
% 0.43/0.61          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61         sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['34', '40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (m1_subset_1 @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (![X14 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X14 @ sk_B_1)
% 0.43/0.61          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.43/0.61              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X14)))
% 0.43/0.61              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X14))
% 0.43/0.61          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.43/0.61          (k2_pre_topc @ sk_A @ 
% 0.43/0.61           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.43/0.61          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.43/0.61        | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.61  thf('46', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.43/0.61      inference('clc', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.43/0.61         (k2_pre_topc @ sk_A @ 
% 0.43/0.61          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.43/0.61         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | (v2_tex_2 @ X11 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.61          | ~ (v3_pre_topc @ X13 @ X12)
% 0.43/0.61          | ((k9_subset_1 @ (u1_struct_0 @ X12) @ X11 @ X13)
% 0.43/0.61              != (k6_domain_1 @ (u1_struct_0 @ X12) @ (sk_C @ X11 @ X12)))
% 0.43/0.61          | ~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12)
% 0.43/0.61          | (v2_struct_0 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.43/0.61          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.43/0.61  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.43/0.61          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | ~ (v3_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['53'])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['42', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['41', '55'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.43/0.61  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['57', '58'])).
% 0.43/0.61  thf('60', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('61', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['59', '60'])).
% 0.43/0.61  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['12', '61'])).
% 0.43/0.61  thf('63', plain, ($false), inference('sup-', [status(thm)], ['9', '62'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
