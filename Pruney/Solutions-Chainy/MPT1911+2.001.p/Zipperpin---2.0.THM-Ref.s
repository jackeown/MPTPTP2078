%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dbae1TIhkf

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:53 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 178 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  629 (2225 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_borsuk_1_type,type,(
    r1_borsuk_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t79_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v1_tdlat_3 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( r1_borsuk_1 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( r1_borsuk_1 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tex_2])).

thf('0',plain,(
    ~ ( r1_borsuk_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v1_tdlat_3 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ? [C: $i] :
              ( ( v3_borsuk_1 @ C @ A @ B )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
              & ( v5_pre_topc @ C @ A @ B )
              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
              & ( v1_funct_1 @ C ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v1_tdlat_3 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_C_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d20_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( r1_borsuk_1 @ A @ B )
          <=> ? [C: $i] :
                ( ( v3_borsuk_1 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v3_borsuk_1 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_borsuk_1 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d20_borsuk_1])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_borsuk_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_funct_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v3_borsuk_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v1_tdlat_3 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v1_funct_1 @ ( sk_C_1 @ X3 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tex_2])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_funct_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v1_tdlat_3 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v1_funct_2 @ ( sk_C_1 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tex_2])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_funct_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v1_tdlat_3 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v5_pre_topc @ ( sk_C_1 @ X3 @ X4 ) @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tex_2])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
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
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v1_tdlat_3 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v3_borsuk_1 @ ( sk_C_1 @ X3 @ X4 ) @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v3_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t78_tex_2])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_borsuk_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_borsuk_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_borsuk_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_borsuk_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_borsuk_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16','28','40','52','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_borsuk_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_borsuk_1 @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dbae1TIhkf
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:53:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 29 iterations in 0.020s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.46  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.18/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.46  thf(r1_borsuk_1_type, type, r1_borsuk_1: $i > $i > $o).
% 0.18/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.46  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.18/0.46  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.18/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.18/0.46  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.18/0.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.18/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.46  thf(t79_tex_2, conjecture,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.18/0.46         ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.18/0.46             ( m1_pre_topc @ B @ A ) ) =>
% 0.18/0.46           ( r1_borsuk_1 @ A @ B ) ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i]:
% 0.18/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.46            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46          ( ![B:$i]:
% 0.18/0.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.18/0.46                ( m1_pre_topc @ B @ A ) ) =>
% 0.18/0.46              ( r1_borsuk_1 @ A @ B ) ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t79_tex_2])).
% 0.18/0.46  thf('0', plain, (~ (r1_borsuk_1 @ sk_A @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(t78_tex_2, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.18/0.46         ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.18/0.46             ( m1_pre_topc @ B @ A ) ) =>
% 0.18/0.46           ( ?[C:$i]:
% 0.18/0.46             ( ( v3_borsuk_1 @ C @ A @ B ) & 
% 0.18/0.46               ( m1_subset_1 @
% 0.18/0.46                 C @ 
% 0.18/0.46                 ( k1_zfmisc_1 @
% 0.18/0.46                   ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.18/0.46               ( v5_pre_topc @ C @ A @ B ) & 
% 0.18/0.46               ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.18/0.46               ( v1_funct_1 @ C ) ) ) ) ) ))).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X3)
% 0.18/0.46          | ~ (v1_tdlat_3 @ X3)
% 0.18/0.46          | ~ (m1_pre_topc @ X3 @ X4)
% 0.18/0.46          | (m1_subset_1 @ (sk_C_1 @ X3 @ X4) @ 
% 0.18/0.46             (k1_zfmisc_1 @ 
% 0.18/0.46              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X3))))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v3_tdlat_3 @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t78_tex_2])).
% 0.18/0.46  thf('3', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (v3_tdlat_3 @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.18/0.46           (k1_zfmisc_1 @ 
% 0.18/0.46            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.18/0.46        | ~ (v1_tdlat_3 @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.46  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('5', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('7', plain, ((v1_tdlat_3 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.18/0.46           (k1_zfmisc_1 @ 
% 0.18/0.46            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.18/0.46  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_B)
% 0.18/0.46        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.18/0.46           (k1_zfmisc_1 @ 
% 0.18/0.46            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.18/0.46      inference('clc', [status(thm)], ['8', '9'])).
% 0.18/0.46  thf('11', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('12', plain,
% 0.18/0.46      ((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.18/0.46        (k1_zfmisc_1 @ 
% 0.18/0.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.18/0.46      inference('clc', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf(d20_borsuk_1, axiom,
% 0.18/0.46    (![A:$i]:
% 0.18/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.46       ( ![B:$i]:
% 0.18/0.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.18/0.46           ( ( r1_borsuk_1 @ A @ B ) <=>
% 0.18/0.46             ( ?[C:$i]:
% 0.18/0.46               ( ( v3_borsuk_1 @ C @ A @ B ) & 
% 0.18/0.46                 ( m1_subset_1 @
% 0.18/0.46                   C @ 
% 0.18/0.46                   ( k1_zfmisc_1 @
% 0.18/0.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.18/0.46                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.18/0.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.18/0.46                 ( v1_funct_1 @ C ) ) ) ) ) ) ))).
% 0.18/0.46  thf('13', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X0)
% 0.18/0.46          | ~ (m1_pre_topc @ X0 @ X1)
% 0.18/0.46          | ~ (v3_borsuk_1 @ X2 @ X1 @ X0)
% 0.18/0.46          | ~ (m1_subset_1 @ X2 @ 
% 0.18/0.46               (k1_zfmisc_1 @ 
% 0.18/0.46                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.18/0.46          | ~ (v5_pre_topc @ X2 @ X1 @ X0)
% 0.18/0.46          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.18/0.46          | ~ (v1_funct_1 @ X2)
% 0.18/0.46          | (r1_borsuk_1 @ X1 @ X0)
% 0.18/0.46          | ~ (l1_pre_topc @ X1)
% 0.18/0.46          | ~ (v2_pre_topc @ X1)
% 0.18/0.46          | (v2_struct_0 @ X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [d20_borsuk_1])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (r1_borsuk_1 @ sk_A @ sk_B)
% 0.18/0.46        | ~ (v1_funct_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.18/0.46        | ~ (v1_funct_2 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.46             (u1_struct_0 @ sk_B))
% 0.18/0.46        | ~ (v5_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.18/0.46        | ~ (v3_borsuk_1 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.18/0.46        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.46  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('18', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X3)
% 0.18/0.46          | ~ (v1_tdlat_3 @ X3)
% 0.18/0.46          | ~ (m1_pre_topc @ X3 @ X4)
% 0.18/0.46          | (v1_funct_1 @ (sk_C_1 @ X3 @ X4))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v3_tdlat_3 @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t78_tex_2])).
% 0.18/0.46  thf('19', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (v3_tdlat_3 @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (v1_funct_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.18/0.46        | ~ (v1_tdlat_3 @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.18/0.46  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('21', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('23', plain, ((v1_tdlat_3 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('24', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (v1_funct_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.18/0.46  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('26', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_B) | (v1_funct_1 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.18/0.46      inference('clc', [status(thm)], ['24', '25'])).
% 0.18/0.46  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('28', plain, ((v1_funct_1 @ (sk_C_1 @ sk_B @ sk_A))),
% 0.18/0.46      inference('clc', [status(thm)], ['26', '27'])).
% 0.18/0.46  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('30', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X3)
% 0.18/0.46          | ~ (v1_tdlat_3 @ X3)
% 0.18/0.46          | ~ (m1_pre_topc @ X3 @ X4)
% 0.18/0.46          | (v1_funct_2 @ (sk_C_1 @ X3 @ X4) @ (u1_struct_0 @ X4) @ 
% 0.18/0.46             (u1_struct_0 @ X3))
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v3_tdlat_3 @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t78_tex_2])).
% 0.18/0.46  thf('31', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (v3_tdlat_3 @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (v1_funct_2 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.46           (u1_struct_0 @ sk_B))
% 0.18/0.46        | ~ (v1_tdlat_3 @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.46  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('33', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('35', plain, ((v1_tdlat_3 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('36', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (v1_funct_2 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.46           (u1_struct_0 @ sk_B))
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.18/0.46  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('38', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_B)
% 0.18/0.46        | (v1_funct_2 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.46           (u1_struct_0 @ sk_B)))),
% 0.18/0.46      inference('clc', [status(thm)], ['36', '37'])).
% 0.18/0.46  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('40', plain,
% 0.18/0.46      ((v1_funct_2 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.18/0.46        (u1_struct_0 @ sk_B))),
% 0.18/0.46      inference('clc', [status(thm)], ['38', '39'])).
% 0.18/0.46  thf('41', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('42', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X3)
% 0.18/0.46          | ~ (v1_tdlat_3 @ X3)
% 0.18/0.46          | ~ (m1_pre_topc @ X3 @ X4)
% 0.18/0.46          | (v5_pre_topc @ (sk_C_1 @ X3 @ X4) @ X4 @ X3)
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v3_tdlat_3 @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t78_tex_2])).
% 0.18/0.46  thf('43', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (v3_tdlat_3 @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (v5_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.18/0.46        | ~ (v1_tdlat_3 @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['41', '42'])).
% 0.18/0.46  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('45', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('47', plain, ((v1_tdlat_3 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('48', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (v5_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.18/0.46  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('50', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_B)
% 0.18/0.46        | (v5_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B))),
% 0.18/0.46      inference('clc', [status(thm)], ['48', '49'])).
% 0.18/0.46  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('52', plain, ((v5_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.18/0.46      inference('clc', [status(thm)], ['50', '51'])).
% 0.18/0.46  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('54', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((v2_struct_0 @ X3)
% 0.18/0.46          | ~ (v1_tdlat_3 @ X3)
% 0.18/0.46          | ~ (m1_pre_topc @ X3 @ X4)
% 0.18/0.46          | (v3_borsuk_1 @ (sk_C_1 @ X3 @ X4) @ X4 @ X3)
% 0.18/0.46          | ~ (l1_pre_topc @ X4)
% 0.18/0.46          | ~ (v3_tdlat_3 @ X4)
% 0.18/0.46          | ~ (v2_pre_topc @ X4)
% 0.18/0.46          | (v2_struct_0 @ X4))),
% 0.18/0.46      inference('cnf', [status(esa)], [t78_tex_2])).
% 0.18/0.46  thf('55', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.18/0.46        | ~ (v3_tdlat_3 @ sk_A)
% 0.18/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.18/0.46        | (v3_borsuk_1 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.18/0.46        | ~ (v1_tdlat_3 @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['53', '54'])).
% 0.18/0.46  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('57', plain, ((v3_tdlat_3 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('59', plain, ((v1_tdlat_3 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('60', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (v3_borsuk_1 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.18/0.46  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('62', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_B)
% 0.18/0.46        | (v3_borsuk_1 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B))),
% 0.18/0.46      inference('clc', [status(thm)], ['60', '61'])).
% 0.18/0.46  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('64', plain, ((v3_borsuk_1 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.18/0.46      inference('clc', [status(thm)], ['62', '63'])).
% 0.18/0.46  thf('65', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('66', plain,
% 0.18/0.46      (((v2_struct_0 @ sk_A)
% 0.18/0.46        | (r1_borsuk_1 @ sk_A @ sk_B)
% 0.18/0.46        | (v2_struct_0 @ sk_B))),
% 0.18/0.46      inference('demod', [status(thm)],
% 0.18/0.46                ['14', '15', '16', '28', '40', '52', '64', '65'])).
% 0.18/0.46  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('68', plain, (((v2_struct_0 @ sk_B) | (r1_borsuk_1 @ sk_A @ sk_B))),
% 0.18/0.46      inference('clc', [status(thm)], ['66', '67'])).
% 0.18/0.46  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('70', plain, ((r1_borsuk_1 @ sk_A @ sk_B)),
% 0.18/0.46      inference('clc', [status(thm)], ['68', '69'])).
% 0.18/0.46  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
