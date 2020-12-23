%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ArFxuixA4k

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:13 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 206 expanded)
%              Number of leaves         :   36 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  922 (2139 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf('0',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X22 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( X20 = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('35',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ X9 @ X9 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('40',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('43',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('45',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ~ ( v1_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_tops_1 @ X0 @ sk_A )
        | ~ ( v2_tex_2 @ X0 @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_tops_1 @ X0 @ sk_A )
        | ~ ( v2_tex_2 @ X0 @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( v1_tops_1 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X12: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_pre_topc @ X17 @ X16 )
       != ( u1_struct_0 @ X17 ) )
      | ( v1_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( v1_tops_1 @ sk_B @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('79',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77','80'])).

thf('82',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','60','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ArFxuixA4k
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 254 iterations in 0.133s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.39/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.59  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.39/0.59  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.59  thf(t49_tex_2, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.39/0.59         ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.59             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.59            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59              ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.59                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.39/0.59       ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf(dt_k2_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.59  thf('3', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.59  thf('4', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.39/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf(t43_tex_2, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.39/0.59         ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.39/0.59          | (v2_tex_2 @ X23 @ X24)
% 0.39/0.59          | ~ (l1_pre_topc @ X24)
% 0.39/0.59          | ~ (v1_tdlat_3 @ X24)
% 0.39/0.59          | ~ (v2_pre_topc @ X24)
% 0.39/0.59          | (v2_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X0)
% 0.39/0.59          | ~ (v2_pre_topc @ X0)
% 0.39/0.59          | ~ (v1_tdlat_3 @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.59  thf('7', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.39/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('9', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['8'])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d7_tex_2, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( v3_tex_2 @ B @ A ) <=>
% 0.39/0.59             ( ( v2_tex_2 @ B @ A ) & 
% 0.39/0.59               ( ![C:$i]:
% 0.39/0.59                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.59                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.59          | ~ (v3_tex_2 @ X20 @ X21)
% 0.39/0.59          | ~ (v2_tex_2 @ X22 @ X21)
% 0.39/0.59          | ~ (r1_tarski @ X20 @ X22)
% 0.39/0.59          | ((X20) = (X22))
% 0.39/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.39/0.59          | ~ (l1_pre_topc @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ sk_A)
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | ((sk_B) = (X0))
% 0.39/0.59          | ~ (r1_tarski @ sk_B @ X0)
% 0.39/0.59          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.59          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | ((sk_B) = (X0))
% 0.39/0.59          | ~ (r1_tarski @ sk_B @ X0)
% 0.39/0.59          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.59          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.59           | ~ (r1_tarski @ sk_B @ X0)
% 0.39/0.59           | ((sk_B) = (X0))
% 0.39/0.59           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['9', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.39/0.59         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.59         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.39/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '15'])).
% 0.39/0.59  thf(d3_tarski, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X1 : $i, X3 : $i]:
% 0.39/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(l3_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X6 @ X7)
% 0.39/0.59          | (r2_hidden @ X6 @ X8)
% 0.39/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r1_tarski @ sk_B @ X0)
% 0.39/0.59          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['17', '20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X1 : $i, X3 : $i]:
% 0.39/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.59  thf('24', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.39/0.59         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.39/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['16', '24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.59         | ~ (v1_tdlat_3 @ sk_A)
% 0.39/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59         | (v2_struct_0 @ sk_A)
% 0.39/0.59         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '25'])).
% 0.39/0.59  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.39/0.59  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('clc', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.39/0.59         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (((v1_subset_1 @ sk_B @ sk_B))
% 0.39/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.39/0.59             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf(fc14_subset_1, axiom,
% 0.39/0.59    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.39/0.59  thf('35', plain, (![X9 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X9) @ X9)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.39/0.59  thf('36', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.59  thf('37', plain, (![X9 : $i]: ~ (v1_subset_1 @ X9 @ X9)),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.39/0.59       ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['34', '37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.39/0.59       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('split', [status(esa)], ['8'])).
% 0.39/0.59  thf('40', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.39/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d7_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X18 : $i, X19 : $i]:
% 0.39/0.59         (((X19) = (X18))
% 0.39/0.59          | (v1_subset_1 @ X19 @ X18)
% 0.39/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['8'])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf(t48_tex_2, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.39/0.59             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      (![X25 : $i, X26 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.39/0.59          | (v3_tex_2 @ X25 @ X26)
% 0.39/0.59          | ~ (v2_tex_2 @ X25 @ X26)
% 0.39/0.59          | ~ (v1_tops_1 @ X25 @ X26)
% 0.39/0.59          | ~ (l1_pre_topc @ X26)
% 0.39/0.59          | ~ (v2_pre_topc @ X26)
% 0.39/0.59          | (v2_struct_0 @ X26))),
% 0.39/0.59      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.39/0.59           | (v2_struct_0 @ sk_A)
% 0.39/0.59           | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59           | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59           | ~ (v1_tops_1 @ X0 @ sk_A)
% 0.39/0.59           | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.59           | (v3_tex_2 @ X0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.39/0.59           | (v2_struct_0 @ sk_A)
% 0.39/0.59           | ~ (v1_tops_1 @ X0 @ sk_A)
% 0.39/0.59           | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.59           | (v3_tex_2 @ X0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.39/0.59         | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.39/0.59         | ~ (v1_tops_1 @ sk_B @ sk_A)
% 0.39/0.59         | (v2_struct_0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['40', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('53', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.39/0.59          | (v2_tex_2 @ X23 @ X24)
% 0.39/0.59          | ~ (l1_pre_topc @ X24)
% 0.39/0.59          | ~ (v1_tdlat_3 @ X24)
% 0.39/0.59          | ~ (v2_pre_topc @ X24)
% 0.39/0.59          | (v2_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59        | ~ (v1_tdlat_3 @ sk_A)
% 0.39/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.59  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('56', plain, ((v1_tdlat_3 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('58', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.39/0.59  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('60', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.59      inference('clc', [status(thm)], ['58', '59'])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf(fc4_pre_topc, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (![X12 : $i]:
% 0.39/0.59         ((v4_pre_topc @ (k2_struct_0 @ X12) @ X12)
% 0.39/0.59          | ~ (l1_pre_topc @ X12)
% 0.39/0.59          | ~ (v2_pre_topc @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.39/0.59  thf(d3_struct_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.59  thf('63', plain,
% 0.39/0.59      (![X10 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('64', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.39/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf(t52_pre_topc, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.39/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.39/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.59          | ~ (v4_pre_topc @ X13 @ X14)
% 0.39/0.59          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.39/0.59          | ~ (l1_pre_topc @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ X0)
% 0.39/0.59          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.39/0.59          | ~ (l1_struct_0 @ X0)
% 0.39/0.59          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (l1_pre_topc @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['63', '66'])).
% 0.39/0.59  thf('68', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v2_pre_topc @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (l1_struct_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['62', '67'])).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_struct_0 @ X0)
% 0.39/0.59          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (v2_pre_topc @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.39/0.59  thf('70', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.39/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf(d2_tops_3, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( v1_tops_1 @ B @ A ) <=>
% 0.39/0.59             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.39/0.59          | ((k2_pre_topc @ X17 @ X16) != (u1_struct_0 @ X17))
% 0.39/0.59          | (v1_tops_1 @ X16 @ X17)
% 0.39/0.59          | ~ (l1_pre_topc @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.39/0.59  thf('72', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ X0)
% 0.39/0.59          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.59          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (u1_struct_0 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.59  thf('73', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((u1_struct_0 @ X0) != (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (v2_pre_topc @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (l1_struct_0 @ X0)
% 0.39/0.59          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['69', '72'])).
% 0.39/0.59  thf('74', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.39/0.59          | ~ (l1_struct_0 @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (v2_pre_topc @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['73'])).
% 0.39/0.59  thf('75', plain,
% 0.39/0.59      ((((v1_tops_1 @ sk_B @ sk_A)
% 0.39/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup+', [status(thm)], ['61', '74'])).
% 0.39/0.59  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_l1_pre_topc, axiom,
% 0.39/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.59  thf('79', plain,
% 0.39/0.59      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.59  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.59  thf('81', plain,
% 0.39/0.59      (((v1_tops_1 @ sk_B @ sk_A))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['75', '76', '77', '80'])).
% 0.39/0.59  thf('82', plain,
% 0.39/0.59      ((((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['51', '60', '81'])).
% 0.39/0.59  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('84', plain,
% 0.39/0.59      (((v3_tex_2 @ sk_B @ sk_A))
% 0.39/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('clc', [status(thm)], ['82', '83'])).
% 0.39/0.59  thf('85', plain,
% 0.39/0.59      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('86', plain,
% 0.39/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.39/0.59       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['84', '85'])).
% 0.39/0.59  thf('87', plain, ($false),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '86'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
