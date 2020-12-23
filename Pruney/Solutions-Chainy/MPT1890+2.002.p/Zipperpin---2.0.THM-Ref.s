%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lgSrRDXVW3

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 198 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  833 (4139 expanded)
%              Number of equality atoms :    9 (  91 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v2_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ X4 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X13 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X11 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 @ X12 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X11 ) @ ( sk_C @ X10 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('52',plain,
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
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['12','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['9','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lgSrRDXVW3
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 73 iterations in 0.060s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(t58_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ![C:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                 ( ( r2_hidden @ C @ B ) =>
% 0.21/0.52                   ( ( k9_subset_1 @
% 0.21/0.52                       ( u1_struct_0 @ A ) @ B @ 
% 0.21/0.52                       ( k2_pre_topc @
% 0.21/0.52                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.21/0.52                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.21/0.52             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ( ![C:$i]:
% 0.21/0.52                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                    ( ( r2_hidden @ C @ B ) =>
% 0.21/0.52                      ( ( k9_subset_1 @
% 0.21/0.52                          ( u1_struct_0 @ A ) @ B @ 
% 0.21/0.52                          ( k2_pre_topc @
% 0.21/0.52                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.21/0.52                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.21/0.52                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t35_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X8)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | (v2_tex_2 @ X8 @ X9)
% 0.21/0.52          | ~ (l1_pre_topc @ X9)
% 0.21/0.52          | ~ (v2_pre_topc @ X9)
% 0.21/0.52          | (v2_struct_0 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.52  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain, ((~ (v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_subset_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.52          | (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t57_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ![C:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.52                      ( ![D:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @
% 0.21/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.52                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.52                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.52             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | (v2_tex_2 @ X10 @ X11)
% 0.21/0.52          | (m1_subset_1 @ (sk_C @ X10 @ X11) @ (u1_struct_0 @ X11))
% 0.21/0.52          | ~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11)
% 0.21/0.52          | (v2_struct_0 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('17', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.52  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf(dt_k6_domain_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X4)
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ X4)
% 0.21/0.52          | (m1_subset_1 @ (k6_domain_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((m1_subset_1 @ 
% 0.21/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(fc1_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X6)
% 0.21/0.52          | ~ (v2_pre_topc @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.52          | (v4_pre_topc @ (k2_pre_topc @ X6 @ X7) @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v4_pre_topc @ 
% 0.21/0.52           (k2_pre_topc @ sk_A @ 
% 0.21/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52           sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v4_pre_topc @ 
% 0.21/0.52           (k2_pre_topc @ sk_A @ 
% 0.21/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52           sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((m1_subset_1 @ 
% 0.21/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(dt_k2_pre_topc, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X2)
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.52          | (m1_subset_1 @ (k2_pre_topc @ X2 @ X3) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (k2_pre_topc @ sk_A @ 
% 0.21/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (k2_pre_topc @ sk_A @ 
% 0.21/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X13 @ sk_B)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X13)))
% 0.21/0.52              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X13))
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52          (k2_pre_topc @ sk_A @ 
% 0.21/0.52           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.21/0.52          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.52        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | (v2_tex_2 @ X10 @ X11)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X10 @ X11) @ X10)
% 0.21/0.52          | ~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11)
% 0.21/0.52          | (v2_struct_0 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.21/0.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((v2_tex_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.52      inference('clc', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52         (k2_pre_topc @ sk_A @ 
% 0.21/0.52          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.21/0.52         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | (v2_tex_2 @ X10 @ X11)
% 0.21/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | ~ (v4_pre_topc @ X12 @ X11)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X11) @ X10 @ X12)
% 0.21/0.52              != (k6_domain_1 @ (u1_struct_0 @ X11) @ (sk_C @ X10 @ X11)))
% 0.21/0.52          | ~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11)
% 0.21/0.52          | (v2_struct_0 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v4_pre_topc @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.21/0.52          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v4_pre_topc @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (((v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | ~ (m1_subset_1 @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (v4_pre_topc @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v4_pre_topc @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ 
% 0.21/0.52              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.21/0.52             sk_A)
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '59'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.52  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('64', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '65'])).
% 0.21/0.52  thf('67', plain, ($false), inference('demod', [status(thm)], ['9', '66'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
