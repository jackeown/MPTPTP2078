%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OLE22juU3i

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:52 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 167 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  601 (1567 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
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
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
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

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X12 @ X11 ) )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ~ ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('25',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tdlat_3 @ X18 )
      | ( v2_tex_2 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tdlat_3 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['34','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['15','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OLE22juU3i
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.52/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.75  % Solved by: fo/fo7.sh
% 0.52/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.75  % done 327 iterations in 0.295s
% 0.52/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.75  % SZS output start Refutation
% 0.52/0.75  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.52/0.75  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.52/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.75  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.52/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.75  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.52/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.75  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.52/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.75  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.52/0.75  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.52/0.75  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.52/0.75  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.75  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.52/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.75  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.52/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.75  thf(t43_tex_2, conjecture,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.52/0.75         ( l1_pre_topc @ A ) ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.75           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.52/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.75    (~( ![A:$i]:
% 0.52/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.52/0.75            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.75          ( ![B:$i]:
% 0.52/0.75            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.75              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.52/0.75    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.52/0.75  thf('0', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(t37_tex_2, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.75           ( ( ![C:$i]:
% 0.52/0.75               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.75                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.52/0.75                      ( ![D:$i]:
% 0.52/0.75                        ( ( m1_subset_1 @
% 0.52/0.75                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.75                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.52/0.75                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.52/0.75                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.52/0.75             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.52/0.75  thf('1', plain,
% 0.52/0.75      (![X21 : $i, X22 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.52/0.75          | (v2_tex_2 @ X21 @ X22)
% 0.52/0.75          | (r2_hidden @ (sk_C @ X21 @ X22) @ X21)
% 0.52/0.75          | ~ (l1_pre_topc @ X22)
% 0.52/0.75          | ~ (v2_pre_topc @ X22)
% 0.52/0.75          | (v2_struct_0 @ X22))),
% 0.52/0.75      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.52/0.75  thf('2', plain,
% 0.52/0.75      (((v2_struct_0 @ sk_A)
% 0.52/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.52/0.75        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.75        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.52/0.75        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.52/0.75      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.75  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('5', plain,
% 0.52/0.75      (((v2_struct_0 @ sk_A)
% 0.52/0.75        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.52/0.75        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.52/0.75  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('7', plain,
% 0.52/0.75      (((v2_tex_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.52/0.75      inference('clc', [status(thm)], ['5', '6'])).
% 0.52/0.75  thf('8', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('9', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.52/0.75      inference('clc', [status(thm)], ['7', '8'])).
% 0.52/0.75  thf(dt_k2_subset_1, axiom,
% 0.52/0.75    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.75  thf('10', plain,
% 0.52/0.75      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.52/0.75  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.52/0.75  thf('11', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.52/0.75      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.52/0.75  thf('12', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.52/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.75  thf(t5_subset, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.52/0.75          ( v1_xboole_0 @ C ) ) ))).
% 0.52/0.75  thf('13', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.75         (~ (r2_hidden @ X2 @ X3)
% 0.52/0.75          | ~ (v1_xboole_0 @ X4)
% 0.52/0.75          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t5_subset])).
% 0.52/0.75  thf('14', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.75  thf('15', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.75      inference('sup-', [status(thm)], ['9', '14'])).
% 0.52/0.75  thf('16', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(t29_pre_topc, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( l1_pre_topc @ A ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.75           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.52/0.75  thf('17', plain,
% 0.52/0.75      (![X11 : $i, X12 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.52/0.75          | ((u1_struct_0 @ (k1_pre_topc @ X12 @ X11)) = (X11))
% 0.52/0.75          | ~ (l1_pre_topc @ X12))),
% 0.52/0.75      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.52/0.75  thf('18', plain,
% 0.52/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.75        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.75  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('20', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['18', '19'])).
% 0.52/0.75  thf(fc1_struct_0, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.52/0.75       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.52/0.75  thf('21', plain,
% 0.52/0.75      (![X10 : $i]:
% 0.52/0.75         ((v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.52/0.75          | ~ (l1_struct_0 @ X10)
% 0.52/0.75          | ~ (v2_struct_0 @ X10))),
% 0.52/0.75      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.52/0.75  thf('22', plain,
% 0.52/0.75      (((v1_xboole_0 @ sk_B)
% 0.52/0.75        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.52/0.75        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('23', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(dt_k1_pre_topc, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( l1_pre_topc @ A ) & 
% 0.52/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.75       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.52/0.75         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.52/0.75  thf('24', plain,
% 0.52/0.75      (![X5 : $i, X6 : $i]:
% 0.52/0.75         (~ (l1_pre_topc @ X5)
% 0.52/0.75          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.52/0.75          | (m1_pre_topc @ (k1_pre_topc @ X5 @ X6) @ X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.52/0.75  thf('25', plain,
% 0.52/0.75      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.52/0.75        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.75  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('27', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.52/0.75      inference('demod', [status(thm)], ['25', '26'])).
% 0.52/0.75  thf(dt_m1_pre_topc, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( l1_pre_topc @ A ) =>
% 0.52/0.75       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.52/0.75  thf('28', plain,
% 0.52/0.75      (![X8 : $i, X9 : $i]:
% 0.52/0.75         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.52/0.75  thf('29', plain,
% 0.52/0.75      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.75  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('31', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.75  thf(dt_l1_pre_topc, axiom,
% 0.52/0.75    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.52/0.75  thf('32', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.75  thf('33', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.75  thf('34', plain,
% 0.52/0.75      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('demod', [status(thm)], ['22', '33'])).
% 0.52/0.75  thf('35', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('36', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['18', '19'])).
% 0.52/0.75  thf(t26_tex_2, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.75           ( ![C:$i]:
% 0.52/0.75             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.75               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.52/0.75                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.52/0.75  thf('37', plain,
% 0.52/0.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.75         ((v2_struct_0 @ X18)
% 0.52/0.75          | ~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.75          | ((X20) != (u1_struct_0 @ X18))
% 0.52/0.75          | ~ (v1_tdlat_3 @ X18)
% 0.52/0.75          | (v2_tex_2 @ X20 @ X19)
% 0.52/0.75          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.75          | ~ (l1_pre_topc @ X19)
% 0.52/0.75          | (v2_struct_0 @ X19))),
% 0.52/0.75      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.52/0.75  thf('38', plain,
% 0.52/0.75      (![X18 : $i, X19 : $i]:
% 0.52/0.75         ((v2_struct_0 @ X19)
% 0.52/0.75          | ~ (l1_pre_topc @ X19)
% 0.52/0.75          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.52/0.75               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.75          | (v2_tex_2 @ (u1_struct_0 @ X18) @ X19)
% 0.52/0.75          | ~ (v1_tdlat_3 @ X18)
% 0.52/0.75          | ~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.75          | (v2_struct_0 @ X18))),
% 0.52/0.75      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.75  thf('39', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.52/0.75          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.52/0.75          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.52/0.75          | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.52/0.75          | (v2_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0)
% 0.52/0.75          | ~ (l1_pre_topc @ X0)
% 0.52/0.75          | (v2_struct_0 @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['36', '38'])).
% 0.52/0.75  thf('40', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.52/0.75      inference('demod', [status(thm)], ['25', '26'])).
% 0.52/0.75  thf(cc5_tdlat_3, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.52/0.75         ( l1_pre_topc @ A ) ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( m1_pre_topc @ B @ A ) =>
% 0.52/0.75           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 0.52/0.75             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.52/0.75  thf('41', plain,
% 0.52/0.75      (![X16 : $i, X17 : $i]:
% 0.52/0.75         (~ (m1_pre_topc @ X16 @ X17)
% 0.52/0.75          | (v1_tdlat_3 @ X16)
% 0.52/0.75          | ~ (l1_pre_topc @ X17)
% 0.52/0.75          | ~ (v1_tdlat_3 @ X17)
% 0.52/0.75          | ~ (v2_pre_topc @ X17)
% 0.52/0.75          | (v2_struct_0 @ X17))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 0.52/0.75  thf('42', plain,
% 0.52/0.75      (((v2_struct_0 @ sk_A)
% 0.52/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.52/0.75        | ~ (v1_tdlat_3 @ sk_A)
% 0.52/0.75        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.75        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.75  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('44', plain, ((v1_tdlat_3 @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('46', plain,
% 0.52/0.75      (((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.52/0.75  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('48', plain, ((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.52/0.75      inference('clc', [status(thm)], ['46', '47'])).
% 0.52/0.75  thf('49', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['18', '19'])).
% 0.52/0.75  thf('50', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.52/0.75          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.52/0.75          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.52/0.75          | (v2_tex_2 @ sk_B @ X0)
% 0.52/0.75          | ~ (l1_pre_topc @ X0)
% 0.52/0.75          | (v2_struct_0 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['39', '48', '49'])).
% 0.52/0.75  thf('51', plain,
% 0.52/0.75      (((v2_struct_0 @ sk_A)
% 0.52/0.75        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.75        | (v2_tex_2 @ sk_B @ sk_A)
% 0.52/0.75        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.52/0.75        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['35', '50'])).
% 0.52/0.75  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('53', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.52/0.75      inference('demod', [status(thm)], ['25', '26'])).
% 0.52/0.75  thf('54', plain,
% 0.52/0.75      (((v2_struct_0 @ sk_A)
% 0.52/0.75        | (v2_tex_2 @ sk_B @ sk_A)
% 0.52/0.75        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.75      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.52/0.75  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('56', plain,
% 0.52/0.75      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.52/0.75      inference('clc', [status(thm)], ['54', '55'])).
% 0.52/0.75  thf('57', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('58', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.52/0.75      inference('clc', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('59', plain, ((v1_xboole_0 @ sk_B)),
% 0.52/0.75      inference('demod', [status(thm)], ['34', '58'])).
% 0.52/0.75  thf('60', plain, ($false), inference('demod', [status(thm)], ['15', '59'])).
% 0.52/0.75  
% 0.52/0.75  % SZS output end Refutation
% 0.52/0.75  
% 0.63/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
