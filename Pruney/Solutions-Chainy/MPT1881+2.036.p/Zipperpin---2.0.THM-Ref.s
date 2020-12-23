%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q4fwi3TMpu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:17 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  135 (1217 expanded)
%              Number of leaves         :   26 ( 351 expanded)
%              Depth                    :   20
%              Number of atoms          :  972 (13534 expanded)
%              Number of equality atoms :   35 ( 281 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( v1_subset_1 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('2',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('9',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('13',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_tex_2 @ X14 @ X15 )
      | ~ ( v2_tex_2 @ X16 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( X14 = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_subset_1 @ X13 @ X12 )
      | ( X13 != X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('41',plain,(
    ! [X12: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( v1_subset_1 @ X12 @ X12 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ X12 @ X12 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['6','44'])).

thf('46',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( r1_tarski @ X14 @ ( sk_C_1 @ X14 @ X15 ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('61',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('62',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','59','60','61','62','63'])).

thf('65',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('66',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('67',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','44','66'])).

thf('68',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['64','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('73',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( X14
       != ( sk_C_1 @ X14 @ X15 ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
     != ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('78',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('79',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('80',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_B
     != ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81'])).

thf('83',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('84',plain,(
    sk_B
 != ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('87',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('88',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('89',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('90',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','95'])).

thf('97',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['6','44'])).

thf('98',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('100',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','102'])).

thf('104',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['85','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q4fwi3TMpu
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 161 iterations in 0.101s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.38/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.57  thf(t49_tex_2, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.38/0.57         ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.57             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.57            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57              ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.57                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d7_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i]:
% 0.38/0.57         (((X13) = (X12))
% 0.38/0.57          | (v1_subset_1 @ X13 @ X12)
% 0.38/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.38/0.57       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('split', [status(esa)], ['3'])).
% 0.38/0.57  thf(dt_k2_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.57  thf('8', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.57  thf('9', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf(t43_tex_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.38/0.57         ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.57          | (v2_tex_2 @ X19 @ X20)
% 0.38/0.57          | ~ (l1_pre_topc @ X20)
% 0.38/0.57          | ~ (v1_tdlat_3 @ X20)
% 0.38/0.57          | ~ (v2_pre_topc @ X20)
% 0.38/0.57          | (v2_struct_0 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ X0)
% 0.38/0.57          | ~ (v2_pre_topc @ X0)
% 0.38/0.57          | ~ (v1_tdlat_3 @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X0)
% 0.38/0.57          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('12', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['3'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d7_tex_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.57             ( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.57               ( ![C:$i]:
% 0.38/0.57                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.57                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | ~ (v3_tex_2 @ X14 @ X15)
% 0.38/0.57          | ~ (v2_tex_2 @ X16 @ X15)
% 0.38/0.57          | ~ (r1_tarski @ X14 @ X16)
% 0.38/0.57          | ((X14) = (X16))
% 0.38/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | ~ (l1_pre_topc @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ sk_A)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57          | ((sk_B) = (X0))
% 0.38/0.57          | ~ (r1_tarski @ sk_B @ X0)
% 0.38/0.57          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.38/0.57          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57          | ((sk_B) = (X0))
% 0.38/0.57          | ~ (r1_tarski @ sk_B @ X0)
% 0.38/0.57          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.38/0.57          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((![X0 : $i]:
% 0.38/0.57          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.38/0.57           | ~ (r1_tarski @ sk_B @ X0)
% 0.38/0.57           | ((sk_B) = (X0))
% 0.38/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.38/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['12', '19'])).
% 0.38/0.57  thf(d3_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(l3_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.38/0.57          | (r2_hidden @ X9 @ X11)
% 0.38/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ sk_B @ X0)
% 0.38/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '24'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.38/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | ~ (v1_tdlat_3 @ sk_A)
% 0.38/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '29'])).
% 0.38/0.57  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('32', plain, ((v1_tdlat_3 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.38/0.57  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('clc', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (((v1_subset_1 @ sk_B @ sk_B))
% 0.38/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.38/0.57             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['36', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i]:
% 0.38/0.57         (~ (v1_subset_1 @ X13 @ X12)
% 0.38/0.57          | ((X13) != (X12))
% 0.38/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))
% 0.38/0.57          | ~ (v1_subset_1 @ X12 @ X12))),
% 0.38/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.57  thf('42', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('43', plain, (![X12 : $i]: ~ (v1_subset_1 @ X12 @ X12)),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.38/0.57       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['39', '43'])).
% 0.38/0.57  thf('45', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['6', '44'])).
% 0.38/0.57  thf('46', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('47', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | ~ (v2_tex_2 @ X14 @ X15)
% 0.38/0.57          | (r1_tarski @ X14 @ (sk_C_1 @ X14 @ X15))
% 0.38/0.57          | (v3_tex_2 @ X14 @ X15)
% 0.38/0.57          | ~ (l1_pre_topc @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X0)
% 0.38/0.57          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.38/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.38/0.57             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.38/0.57          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      ((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.57        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57           (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_A))
% 0.38/0.57        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '49'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.57          | (v2_tex_2 @ X19 @ X20)
% 0.38/0.57          | ~ (l1_pre_topc @ X20)
% 0.38/0.57          | ~ (v1_tdlat_3 @ X20)
% 0.38/0.57          | ~ (v2_pre_topc @ X20)
% 0.38/0.57          | (v2_struct_0 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57        | ~ (v1_tdlat_3 @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('55', plain, ((v1_tdlat_3 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('57', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.38/0.57  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('59', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['57', '58'])).
% 0.38/0.57  thf('60', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('61', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('62', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (((r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['50', '59', '60', '61', '62', '63'])).
% 0.38/0.57  thf('65', plain,
% 0.38/0.57      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['37'])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.38/0.57       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['37'])).
% 0.38/0.57  thf('67', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['6', '44', '66'])).
% 0.38/0.57  thf('68', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.38/0.57  thf('69', plain, ((r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['64', '68'])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      (![X4 : $i, X6 : $i]:
% 0.38/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('71', plain,
% 0.38/0.57      ((~ (r1_tarski @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.57        | ((sk_C_1 @ sk_B @ sk_A) = (sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.57  thf('72', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('73', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('74', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | ~ (v2_tex_2 @ X14 @ X15)
% 0.38/0.57          | ((X14) != (sk_C_1 @ X14 @ X15))
% 0.38/0.57          | (v3_tex_2 @ X14 @ X15)
% 0.38/0.57          | ~ (l1_pre_topc @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.57  thf('75', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X0)
% 0.38/0.57          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.38/0.57          | ((u1_struct_0 @ X0) != (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.38/0.57          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      ((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.57        | ((u1_struct_0 @ sk_A) != (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_A))
% 0.38/0.57        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['72', '75'])).
% 0.38/0.57  thf('77', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['57', '58'])).
% 0.38/0.57  thf('78', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('79', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('80', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.38/0.57  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('82', plain,
% 0.38/0.57      ((((sk_B) != (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77', '78', '79', '80', '81'])).
% 0.38/0.57  thf('83', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.38/0.57  thf('84', plain, (((sk_B) != (sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['82', '83'])).
% 0.38/0.57  thf('85', plain, (~ (r1_tarski @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['71', '84'])).
% 0.38/0.57  thf('86', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('87', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['57', '58'])).
% 0.38/0.57  thf('88', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('89', plain,
% 0.38/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | ~ (v2_tex_2 @ X14 @ X15)
% 0.38/0.57          | (m1_subset_1 @ (sk_C_1 @ X14 @ X15) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | (v3_tex_2 @ X14 @ X15)
% 0.38/0.57          | ~ (l1_pre_topc @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.57  thf('91', plain,
% 0.38/0.57      ((![X0 : $i]:
% 0.38/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.38/0.57           | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57           | (v3_tex_2 @ X0 @ sk_A)
% 0.38/0.57           | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ 
% 0.38/0.57              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.57  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('93', plain,
% 0.38/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.57  thf('94', plain,
% 0.38/0.57      ((![X0 : $i]:
% 0.38/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.38/0.57           | (v3_tex_2 @ X0 @ sk_A)
% 0.38/0.57           | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.38/0.57           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.38/0.57  thf('95', plain,
% 0.38/0.57      (((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.57         | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.38/0.57         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['88', '94'])).
% 0.38/0.57  thf('96', plain,
% 0.38/0.57      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.57         | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))))
% 0.38/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['87', '95'])).
% 0.38/0.57  thf('97', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['6', '44'])).
% 0.38/0.57  thf('98', plain,
% 0.38/0.57      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.57        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B)))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.38/0.57  thf('99', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.38/0.57  thf('100', plain,
% 0.38/0.57      ((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.57      inference('clc', [status(thm)], ['98', '99'])).
% 0.38/0.57  thf('101', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.38/0.57          | (r2_hidden @ X9 @ X11)
% 0.38/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.57  thf('102', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['100', '101'])).
% 0.38/0.57  thf('103', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ (sk_C_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.57          | (r2_hidden @ (sk_C @ X0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['86', '102'])).
% 0.38/0.57  thf('104', plain,
% 0.38/0.57      (![X1 : $i, X3 : $i]:
% 0.38/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('105', plain,
% 0.38/0.57      (((r1_tarski @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.57        | (r1_tarski @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.57  thf('106', plain, ((r1_tarski @ (sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 0.38/0.57      inference('simplify', [status(thm)], ['105'])).
% 0.38/0.57  thf('107', plain, ($false), inference('demod', [status(thm)], ['85', '106'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
