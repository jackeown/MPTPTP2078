%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xGeEpKhfTJ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 201 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  771 (4265 expanded)
%              Number of equality atoms :    9 (  94 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v2_tex_2 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X9 @ X10 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tdlat_3 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v2_tex_2 @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tdlat_3 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('38',plain,(
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X12 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('41',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v2_tex_2 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X10 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X10 ) @ X9 @ X11 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X10 ) @ ( sk_C @ X9 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tdlat_3 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('43',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','56'])).

thf('58',plain,(
    $false ),
    inference('sup-',[status(thm)],['10','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xGeEpKhfTJ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 72 iterations in 0.059s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(t58_tex_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                 ( ( r2_hidden @ C @ B ) =>
% 0.20/0.52                   ( ( k9_subset_1 @
% 0.20/0.52                       ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.52                       ( k2_pre_topc @
% 0.20/0.52                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.52                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.20/0.52             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ( ![C:$i]:
% 0.20/0.52                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                    ( ( r2_hidden @ C @ B ) =>
% 0.20/0.52                      ( ( k9_subset_1 @
% 0.20/0.52                          ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.52                          ( k2_pre_topc @
% 0.20/0.52                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.52                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.20/0.52                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t57_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.52                      ( ![D:$i]:
% 0.20/0.52                        ( ( m1_subset_1 @
% 0.20/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.20/0.52                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.52                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.52             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | (v2_tex_2 @ X9 @ X10)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X9 @ X10) @ X9)
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v3_tdlat_3 @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.20/0.52  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t5_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ~ (v1_xboole_0 @ X2)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | (v2_tex_2 @ X9 @ X10)
% 0.20/0.52          | (m1_subset_1 @ (sk_C @ X9 @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v3_tdlat_3 @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.20/0.52  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf(dt_k6_domain_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X5)
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ X5)
% 0.20/0.52          | (m1_subset_1 @ (k6_domain_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((m1_subset_1 @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf(fc1_tops_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X7)
% 0.20/0.52          | ~ (v2_pre_topc @ X7)
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.52          | (v4_pre_topc @ (k2_pre_topc @ X7 @ X8) @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v4_pre_topc @ 
% 0.20/0.52           (k2_pre_topc @ sk_A @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52           sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v4_pre_topc @ 
% 0.20/0.52           (k2_pre_topc @ sk_A @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52           sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((m1_subset_1 @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf(dt_k2_pre_topc, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X3)
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.52          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (m1_subset_1 @ 
% 0.20/0.52           (k2_pre_topc @ sk_A @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (m1_subset_1 @ 
% 0.20/0.52           (k2_pre_topc @ sk_A @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X12 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ sk_B)
% 0.20/0.52          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X12)))
% 0.20/0.52              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X12))
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52          (k2_pre_topc @ sk_A @ 
% 0.20/0.52           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.20/0.52          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.52        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52         (k2_pre_topc @ sk_A @ 
% 0.20/0.52          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.20/0.52         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | (v2_tex_2 @ X9 @ X10)
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (v4_pre_topc @ X11 @ X10)
% 0.20/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X10) @ X9 @ X11)
% 0.20/0.52              != (k6_domain_1 @ (u1_struct_0 @ X10) @ (sk_C @ X9 @ X10)))
% 0.20/0.52          | ~ (l1_pre_topc @ X10)
% 0.20/0.52          | ~ (v3_tdlat_3 @ X10)
% 0.20/0.52          | ~ (v2_pre_topc @ X10)
% 0.20/0.52          | (v2_struct_0 @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52        | ~ (m1_subset_1 @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52        | ~ (m1_subset_1 @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | ~ (m1_subset_1 @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | ~ (v4_pre_topc @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ 
% 0.20/0.52             (k2_pre_topc @ sk_A @ 
% 0.20/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.20/0.52             sk_A)
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.52  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('56', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '56'])).
% 0.20/0.52  thf('58', plain, ($false), inference('sup-', [status(thm)], ['10', '57'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
