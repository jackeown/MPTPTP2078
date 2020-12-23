%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CwcrzEmUBX

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 431 expanded)
%              Number of leaves         :   22 ( 137 expanded)
%              Depth                    :   21
%              Number of atoms          :  728 (7743 expanded)
%              Number of equality atoms :   26 ( 243 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t53_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v3_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ~ ( ( v4_tex_2 @ C @ A )
                      & ( B
                        = ( u1_struct_0 @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( v3_tex_2 @ B @ A )
                & ! [C: $i] :
                    ( ( ~ ( v2_struct_0 @ C )
                      & ( v1_pre_topc @ C )
                      & ( m1_pre_topc @ C @ A ) )
                   => ~ ( ( v4_tex_2 @ C @ A )
                        & ( B
                          = ( u1_struct_0 @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_tex_2 @ X6 @ X7 )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ X6 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_tex_2 @ X0 @ X1 )
      | ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_tex_2 @ X6 @ X7 )
      | ( m1_pre_topc @ ( sk_C_2 @ X6 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( ( sk_C_1 @ X3 @ X4 )
        = ( u1_struct_0 @ X3 ) )
      | ( v4_tex_2 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_tex_2 @ X6 @ X7 )
      | ( X6
        = ( u1_struct_0 @ ( sk_C_2 @ X6 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['28','29','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
      = sk_B )
    | ( v4_tex_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v4_tex_2 @ X8 @ sk_A )
      | ~ ( m1_pre_topc @ X8 @ sk_A )
      | ~ ( v1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_tex_2 @ X6 @ X7 )
      | ( v1_pre_topc @ ( sk_C_2 @ X6 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('58',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('59',plain,
    ( ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['45','56','57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('62',plain,
    ( ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    = sk_B ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v3_tex_2 @ ( sk_C_1 @ X3 @ X4 ) @ X4 )
      | ( v4_tex_2 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('64',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_tex_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v4_tex_2 @ X8 @ sk_A )
      | ~ ( m1_pre_topc @ X8 @ sk_A )
      | ~ ( v1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('74',plain,(
    m1_pre_topc @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('75',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    v2_struct_0 @ ( sk_C_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['15','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CwcrzEmUBX
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 40 iterations in 0.029s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.49  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.49  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.49  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(t53_tex_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49           ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.49                ( ![C:$i]:
% 0.20/0.49                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.49                      ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                    ( ~( ( v4_tex_2 @ C @ A ) & ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49              ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.49                   ( ![C:$i]:
% 0.20/0.49                     ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.49                         ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                       ( ~( ( v4_tex_2 @ C @ A ) & 
% 0.20/0.49                            ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t53_tex_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t34_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.49                ( ![C:$i]:
% 0.20/0.49                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.49                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ~ (v2_tex_2 @ X6 @ X7)
% 0.20/0.49          | ~ (v2_struct_0 @ (sk_C_2 @ X6 @ X7))
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d7_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.49             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.49               ( ![C:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.49                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (v3_tex_2 @ X0 @ X1)
% 0.20/0.49          | (v2_tex_2 @ X0 @ X1)
% 0.20/0.49          | ~ (l1_pre_topc @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.49        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3', '4', '10'])).
% 0.20/0.49  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain, (~ (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ~ (v2_tex_2 @ X6 @ X7)
% 0.20/0.49          | (m1_pre_topc @ (sk_C_2 @ X6 @ X7) @ X7)
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.20/0.49  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf(d8_tex_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( ( v4_tex_2 @ B @ A ) <=>
% 0.20/0.49             ( ![C:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X3 @ X4)
% 0.20/0.49          | ((sk_C_1 @ X3 @ X4) = (u1_struct_0 @ X3))
% 0.20/0.49          | (v4_tex_2 @ X3 @ X4)
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v4_tex_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49            = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ~ (v2_tex_2 @ X6 @ X7)
% 0.20/0.49          | ((X6) = (u1_struct_0 @ (sk_C_2 @ X6 @ X7)))
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ((sk_B) = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A)))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((sk_B) = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A)))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.49  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B)
% 0.20/0.49        | ((sk_B) = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, (((sk_B) = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v4_tex_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) = (sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29', '40'])).
% 0.20/0.49  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) = (sk_B))
% 0.20/0.49        | (v4_tex_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X8 : $i]:
% 0.20/0.49         (((sk_B) != (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (v4_tex_2 @ X8 @ sk_A)
% 0.20/0.49          | ~ (m1_pre_topc @ X8 @ sk_A)
% 0.20/0.49          | ~ (v1_pre_topc @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) = (sk_B))
% 0.20/0.49        | (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ((sk_B) != (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X6)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ~ (v2_tex_2 @ X6 @ X7)
% 0.20/0.49          | (v1_pre_topc @ (sk_C_2 @ X6 @ X7))
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.20/0.49  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B) | (v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain, ((v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain, ((m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('58', plain, (((sk_B) = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) = (sk_B))
% 0.20/0.49        | (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_B) != (sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '56', '57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (((v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) = (sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.49  thf('61', plain, (~ (v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('62', plain, (((sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) = (sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X3 @ X4)
% 0.20/0.49          | ~ (v3_tex_2 @ (sk_C_1 @ X3 @ X4) @ X4)
% 0.20/0.49          | (v4_tex_2 @ X3 @ X4)
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((~ (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v4_tex_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ~ (m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('67', plain, ((m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A) | (v4_tex_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.49  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('70', plain, ((v4_tex_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X8 : $i]:
% 0.20/0.49         (((sk_B) != (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (v4_tex_2 @ X8 @ sk_A)
% 0.20/0.49          | ~ (m1_pre_topc @ X8 @ sk_A)
% 0.20/0.49          | ~ (v1_pre_topc @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.49        | ((sk_B) != (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.49  thf('73', plain, ((v1_pre_topc @ (sk_C_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('74', plain, ((m1_pre_topc @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('75', plain, (((sk_B) = (u1_struct_0 @ (sk_C_2 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (((v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A)) | ((sk_B) != (sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.20/0.49  thf('77', plain, ((v2_struct_0 @ (sk_C_2 @ sk_B @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.49  thf('78', plain, ($false), inference('demod', [status(thm)], ['15', '77'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
