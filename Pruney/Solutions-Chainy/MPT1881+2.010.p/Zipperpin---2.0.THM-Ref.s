%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XxbIv3nLS0

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 923 expanded)
%              Number of leaves         :   26 ( 270 expanded)
%              Depth                    :   20
%              Number of atoms          : 1106 (10242 expanded)
%              Number of equality atoms :   36 ( 222 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( v1_subset_1 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('3',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('14',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tex_2 @ X15 @ X16 )
      | ~ ( v2_tex_2 @ X17 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( X15 = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_subset_1 @ X14 @ X13 )
      | ( X14 != X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('42',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X13 @ X13 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('44',plain,(
    ! [X13: $i] :
      ~ ( v1_subset_1 @ X13 @ X13 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['7','45'])).

thf('47',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_C_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('62',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( sk_C_1 @ X15 @ X16 ) )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('76',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('77',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('78',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('79',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( X15
       != ( sk_C_1 @ X15 @ X16 ) )
      | ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
     != ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('93',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('94',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['6','46'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_B
     != ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','91','92','93','94','95'])).

thf('97',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('98',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('99',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','45','98'])).

thf('100',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['97','99'])).

thf('101',plain,(
    sk_B
 != ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['96','100'])).

thf('102',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['77','101'])).

thf('103',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['97','99'])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XxbIv3nLS0
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:09:54 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 133 iterations in 0.081s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.54  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.54  thf(t49_tex_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.54         ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.54            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54              ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.22/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d7_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (((X14) = (X13))
% 0.22/0.54          | (v1_subset_1 @ X14 @ X13)
% 0.22/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.22/0.54       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf(dt_k2_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.54  thf('9', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.54  thf('10', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf(t43_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.54         ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | (v2_tex_2 @ X18 @ X19)
% 0.22/0.54          | ~ (l1_pre_topc @ X19)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X19)
% 0.22/0.54          | ~ (v2_pre_topc @ X19)
% 0.22/0.54          | (v2_struct_0 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d7_tex_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.54             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.54               ( ![C:$i]:
% 0.22/0.54                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.54                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (v3_tex_2 @ X15 @ X16)
% 0.22/0.54          | ~ (v2_tex_2 @ X17 @ X16)
% 0.22/0.54          | ~ (r1_tarski @ X15 @ X17)
% 0.22/0.54          | ((X15) = (X17))
% 0.22/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (l1_pre_topc @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((sk_B) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ sk_B @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | ((sk_B) = (X0))
% 0.22/0.54          | ~ (r1_tarski @ sk_B @ X0)
% 0.22/0.54          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.54           | ~ (r1_tarski @ sk_B @ X0)
% 0.22/0.54           | ((sk_B) = (X0))
% 0.22/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '20'])).
% 0.22/0.54  thf(d3_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(l3_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.54          | (r2_hidden @ X9 @ X11)
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ sk_B @ X0)
% 0.22/0.54          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.54  thf('29', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.22/0.54         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['21', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (((~ (l1_pre_topc @ sk_A)
% 0.22/0.54         | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54         | (v2_struct_0 @ sk_A)
% 0.22/0.54         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '30'])).
% 0.22/0.54  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.22/0.54  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.54        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.22/0.54         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['38'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (((v1_subset_1 @ sk_B @ sk_B))
% 0.22/0.54         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.22/0.54             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['37', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (v1_subset_1 @ X14 @ X13)
% 0.22/0.54          | ((X14) != (X13))
% 0.22/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (![X13 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))
% 0.22/0.54          | ~ (v1_subset_1 @ X13 @ X13))),
% 0.22/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.54  thf('43', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('44', plain, (![X13 : $i]: ~ (v1_subset_1 @ X13 @ X13)),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.22/0.54       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '44'])).
% 0.22/0.54  thf('46', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['7', '45'])).
% 0.22/0.54  thf('47', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('50', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (v2_tex_2 @ X15 @ X16)
% 0.22/0.54          | (m1_subset_1 @ (sk_C_1 @ X15 @ X16) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | (v3_tex_2 @ X15 @ X16)
% 0.22/0.54          | ~ (l1_pre_topc @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['49', '52'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.54          | (r2_hidden @ X9 @ X11)
% 0.22/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (r2_hidden @ X1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X1)
% 0.22/0.54          | (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ 
% 0.22/0.54             (u1_struct_0 @ X0))
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['48', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.22/0.54             (u1_struct_0 @ X0))
% 0.22/0.54          | (r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.22/0.54             (u1_struct_0 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0))
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('62', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (v2_tex_2 @ X15 @ X16)
% 0.22/0.54          | (r1_tarski @ X15 @ (sk_C_1 @ X15 @ X16))
% 0.22/0.54          | (v3_tex_2 @ X15 @ X16)
% 0.22/0.54          | ~ (l1_pre_topc @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.22/0.54             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.22/0.54          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.22/0.54             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['61', '64'])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.22/0.54             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('67', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i]:
% 0.22/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | ~ (r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.22/0.54               (u1_struct_0 @ X0))
% 0.22/0.54          | ((sk_C_1 @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | ((sk_C_1 @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['60', '68'])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((sk_C_1 @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['69'])).
% 0.22/0.54  thf('71', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ((sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['47', '70'])).
% 0.22/0.54  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('73', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('75', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('76', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('77', plain,
% 0.22/0.54      (((v3_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ((sk_C_1 @ sk_B @ sk_A) = (sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 0.22/0.54  thf('78', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('79', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('80', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.54          | ~ (v2_tex_2 @ X15 @ X16)
% 0.22/0.54          | ((X15) != (sk_C_1 @ X15 @ X16))
% 0.22/0.54          | (v3_tex_2 @ X15 @ X16)
% 0.22/0.54          | ~ (l1_pre_topc @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.54  thf('81', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.54          | ((u1_struct_0 @ X0) != (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.22/0.54          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.54  thf('82', plain,
% 0.22/0.54      ((~ (v2_tex_2 @ sk_B @ sk_A)
% 0.22/0.54        | ((u1_struct_0 @ sk_A) != (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_A))
% 0.22/0.54        | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['78', '81'])).
% 0.22/0.54  thf('83', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('84', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | (v2_tex_2 @ X18 @ X19)
% 0.22/0.54          | ~ (l1_pre_topc @ X19)
% 0.22/0.54          | ~ (v1_tdlat_3 @ X19)
% 0.22/0.54          | ~ (v2_pre_topc @ X19)
% 0.22/0.54          | (v2_struct_0 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.22/0.54  thf('85', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.54  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('87', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('89', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.22/0.54  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('91', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('clc', [status(thm)], ['89', '90'])).
% 0.22/0.54  thf('92', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('93', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('94', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '46'])).
% 0.22/0.54  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('96', plain,
% 0.22/0.54      ((((sk_B) != (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['82', '91', '92', '93', '94', '95'])).
% 0.22/0.54  thf('97', plain,
% 0.22/0.54      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['38'])).
% 0.22/0.54  thf('98', plain,
% 0.22/0.54      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.22/0.54       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['38'])).
% 0.22/0.54  thf('99', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['7', '45', '98'])).
% 0.22/0.54  thf('100', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['97', '99'])).
% 0.22/0.54  thf('101', plain, (((sk_B) != (sk_C_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('clc', [status(thm)], ['96', '100'])).
% 0.22/0.54  thf('102', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['77', '101'])).
% 0.22/0.54  thf('103', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['97', '99'])).
% 0.22/0.54  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.54  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
