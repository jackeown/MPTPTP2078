%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WyEY3mUlOB

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:52 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 171 expanded)
%              Number of leaves         :   31 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  732 (1774 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10
        = ( u1_struct_0 @ ( sk_C @ X10 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v1_tdlat_3 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v1_tdlat_3 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v1_tdlat_3 @ X12 )
      | ( v2_tex_2 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v1_tdlat_3 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X10 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['15','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WyEY3mUlOB
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:22:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 96 iterations in 0.092s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(t43_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.37/0.56         ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t37_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.37/0.56                      ( ![D:$i]:
% 0.37/0.56                        ( ( m1_subset_1 @
% 0.37/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.56                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.37/0.56                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.37/0.56             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.56          | (v2_tex_2 @ X15 @ X16)
% 0.37/0.56          | (r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 0.37/0.56          | ~ (l1_pre_topc @ X16)
% 0.37/0.56          | ~ (v2_pre_topc @ X16)
% 0.37/0.56          | (v2_struct_0 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.37/0.56        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.37/0.56        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.37/0.56  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (((v2_tex_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 0.37/0.56      inference('clc', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf(dt_k2_subset_1, axiom,
% 0.37/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.56  thf('11', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.56  thf('12', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf(t5_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.56          | ~ (v1_xboole_0 @ X4)
% 0.37/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t10_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56           ( ?[C:$i]:
% 0.37/0.56             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.37/0.56               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X10)
% 0.37/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.56          | ((X10) = (u1_struct_0 @ (sk_C @ X10 @ X11)))
% 0.37/0.56          | ~ (l1_pre_topc @ X11)
% 0.37/0.56          | (v2_struct_0 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.37/0.56      inference('clc', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X10)
% 0.37/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.56          | (m1_pre_topc @ (sk_C @ X10 @ X11) @ X11)
% 0.37/0.56          | ~ (l1_pre_topc @ X11)
% 0.37/0.56          | (v2_struct_0 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf(cc5_tdlat_3, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.37/0.56         ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 0.37/0.56             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X8 @ X9)
% 0.37/0.56          | (v1_tdlat_3 @ X8)
% 0.37/0.56          | ~ (l1_pre_topc @ X9)
% 0.37/0.56          | ~ (v1_tdlat_3 @ X9)
% 0.37/0.56          | ~ (v2_pre_topc @ X9)
% 0.37/0.56          | (v2_struct_0 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56        | ~ (v1_tdlat_3 @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.56  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.37/0.56  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf(t1_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( m1_subset_1 @
% 0.37/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X5 @ X6)
% 0.37/0.56          | (m1_subset_1 @ (u1_struct_0 @ X5) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (l1_pre_topc @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf(t26_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.37/0.56                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X12)
% 0.37/0.56          | ~ (m1_pre_topc @ X12 @ X13)
% 0.37/0.56          | ((X14) != (u1_struct_0 @ X12))
% 0.37/0.56          | ~ (v1_tdlat_3 @ X12)
% 0.37/0.56          | (v2_tex_2 @ X14 @ X13)
% 0.37/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | ~ (l1_pre_topc @ X13)
% 0.37/0.56          | (v2_struct_0 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X13)
% 0.37/0.56          | ~ (l1_pre_topc @ X13)
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | (v2_tex_2 @ (u1_struct_0 @ X12) @ X13)
% 0.37/0.56          | ~ (v1_tdlat_3 @ X12)
% 0.37/0.56          | ~ (m1_pre_topc @ X12 @ X13)
% 0.37/0.56          | (v2_struct_0 @ X12))),
% 0.37/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['43', '45'])).
% 0.37/0.56  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ sk_A)
% 0.37/0.56        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['38', '48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['37', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (((v2_tex_2 @ sk_B @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['22', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X10)
% 0.37/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.56          | ~ (v2_struct_0 @ (sk_C @ X10 @ X11))
% 0.37/0.56          | ~ (l1_pre_topc @ X11)
% 0.37/0.56          | (v2_struct_0 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.56  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.56  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['59', '60'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (((v2_tex_2 @ sk_B @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['54', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.37/0.56  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('65', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['63', '64'])).
% 0.37/0.56  thf('66', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('67', plain, ((v1_xboole_0 @ sk_B)),
% 0.37/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.37/0.56  thf('68', plain, ($false), inference('demod', [status(thm)], ['15', '67'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
