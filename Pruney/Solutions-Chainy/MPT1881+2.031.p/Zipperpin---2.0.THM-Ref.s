%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c1F3RUpbM5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:16 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 310 expanded)
%              Number of leaves         :   40 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          : 1178 (3340 expanded)
%              Number of equality atoms :   39 (  72 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_tdlat_3 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_tex_2 @ X22 @ X23 )
      | ~ ( v2_tex_2 @ X24 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( X22 = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1 = X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_B_1 = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','31'])).

thf('33',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('42',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ X10 @ X10 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('49',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('51',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tex_2 @ X29 @ X30 )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( v1_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('57',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != ( k2_struct_0 @ X16 ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('63',plain,
    ( ( ( sk_B_1
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('65',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','67','68','69'])).

thf('71',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('72',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('75',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_tdlat_3 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('78',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( v4_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','81'])).

thf('83',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','92'])).

thf('94',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('96',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_tdlat_3 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','94','95','96','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','45','46','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c1F3RUpbM5
% 0.13/0.37  % Computer   : n021.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:17:20 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.70/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.92  % Solved by: fo/fo7.sh
% 0.70/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.92  % done 627 iterations in 0.434s
% 0.70/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.92  % SZS output start Refutation
% 0.70/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.70/0.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.70/0.92  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.70/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.92  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.70/0.92  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.70/0.92  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.70/0.92  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.70/0.92  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.70/0.92  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.70/0.92  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.92  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.70/0.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.92  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.92  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.70/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.92  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.70/0.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.70/0.92  thf(t49_tex_2, conjecture,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.70/0.92         ( l1_pre_topc @ A ) ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( ( v3_tex_2 @ B @ A ) <=>
% 0.70/0.92             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.92    (~( ![A:$i]:
% 0.70/0.92        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.70/0.92            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.92          ( ![B:$i]:
% 0.70/0.92            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92              ( ( v3_tex_2 @ B @ A ) <=>
% 0.70/0.92                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.70/0.92    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.70/0.92  thf('0', plain,
% 0.70/0.92      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('1', plain,
% 0.70/0.92      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.70/0.92       ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('split', [status(esa)], ['0'])).
% 0.70/0.92  thf(dt_k2_subset_1, axiom,
% 0.70/0.92    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.92  thf('2', plain,
% 0.70/0.92      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.70/0.92  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.70/0.92  thf('3', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.70/0.92  thf('4', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(t43_tex_2, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.70/0.92         ( l1_pre_topc @ A ) ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.70/0.92  thf('5', plain,
% 0.70/0.92      (![X27 : $i, X28 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.70/0.92          | (v2_tex_2 @ X27 @ X28)
% 0.70/0.92          | ~ (l1_pre_topc @ X28)
% 0.70/0.92          | ~ (v1_tdlat_3 @ X28)
% 0.70/0.92          | ~ (v2_pre_topc @ X28)
% 0.70/0.92          | (v2_struct_0 @ X28))),
% 0.70/0.92      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.70/0.92  thf('6', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((v2_struct_0 @ X0)
% 0.70/0.92          | ~ (v2_pre_topc @ X0)
% 0.70/0.92          | ~ (v1_tdlat_3 @ X0)
% 0.70/0.92          | ~ (l1_pre_topc @ X0)
% 0.70/0.92          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.92  thf('7', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf('8', plain,
% 0.70/0.92      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('9', plain,
% 0.70/0.92      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('split', [status(esa)], ['8'])).
% 0.70/0.92  thf('10', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(d7_tex_2, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( l1_pre_topc @ A ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( ( v3_tex_2 @ B @ A ) <=>
% 0.70/0.92             ( ( v2_tex_2 @ B @ A ) & 
% 0.70/0.92               ( ![C:$i]:
% 0.70/0.92                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.70/0.92                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.92  thf('11', plain,
% 0.70/0.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.70/0.92          | ~ (v3_tex_2 @ X22 @ X23)
% 0.70/0.92          | ~ (v2_tex_2 @ X24 @ X23)
% 0.70/0.92          | ~ (r1_tarski @ X22 @ X24)
% 0.70/0.92          | ((X22) = (X24))
% 0.70/0.92          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.70/0.92          | ~ (l1_pre_topc @ X23))),
% 0.70/0.92      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.70/0.92  thf('12', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (l1_pre_topc @ sk_A)
% 0.70/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.92          | ((sk_B_1) = (X0))
% 0.70/0.92          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.70/0.92          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.92          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.92  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('14', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.92          | ((sk_B_1) = (X0))
% 0.70/0.92          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.70/0.92          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.92          | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.92  thf('15', plain,
% 0.70/0.92      ((![X0 : $i]:
% 0.70/0.92          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.92           | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.70/0.92           | ((sk_B_1) = (X0))
% 0.70/0.92           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.70/0.92         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['9', '14'])).
% 0.70/0.92  thf('16', plain,
% 0.70/0.92      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.70/0.92         | ~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.70/0.92         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['7', '15'])).
% 0.70/0.92  thf('17', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('18', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(t7_subset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.92       ( ![C:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.92           ( ( ![D:$i]:
% 0.70/0.92               ( ( m1_subset_1 @ D @ A ) =>
% 0.70/0.92                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.70/0.92             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.70/0.92  thf('19', plain,
% 0.70/0.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.70/0.92          | (r1_tarski @ X9 @ X7)
% 0.70/0.92          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.70/0.92          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.70/0.92  thf('20', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.70/0.92          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.70/0.92          | (r1_tarski @ X1 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.70/0.92  thf('21', plain,
% 0.70/0.92      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92        | (r2_hidden @ 
% 0.70/0.92           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.70/0.92           sk_B_1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['17', '20'])).
% 0.70/0.92  thf('22', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(l3_subset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.70/0.92  thf('23', plain,
% 0.70/0.92      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.92         (~ (r2_hidden @ X4 @ X5)
% 0.70/0.92          | (r2_hidden @ X4 @ X6)
% 0.70/0.92          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.70/0.92      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.70/0.92  thf('24', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['22', '23'])).
% 0.70/0.92  thf('25', plain,
% 0.70/0.92      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92        | (r2_hidden @ 
% 0.70/0.92           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.70/0.92           (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['21', '24'])).
% 0.70/0.92  thf('26', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('27', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf('28', plain,
% 0.70/0.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.70/0.92          | (r1_tarski @ X9 @ X7)
% 0.70/0.92          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.70/0.92          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.70/0.92  thf('29', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.70/0.92          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.70/0.92          | (r1_tarski @ X1 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.92  thf('30', plain,
% 0.70/0.92      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92        | ~ (r2_hidden @ 
% 0.70/0.92             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.70/0.92             (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['26', '29'])).
% 0.70/0.92  thf('31', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.70/0.92      inference('clc', [status(thm)], ['25', '30'])).
% 0.70/0.92  thf('32', plain,
% 0.70/0.92      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.70/0.92         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.70/0.92         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('demod', [status(thm)], ['16', '31'])).
% 0.70/0.92  thf('33', plain,
% 0.70/0.92      (((~ (l1_pre_topc @ sk_A)
% 0.70/0.92         | ~ (v1_tdlat_3 @ sk_A)
% 0.70/0.92         | ~ (v2_pre_topc @ sk_A)
% 0.70/0.92         | (v2_struct_0 @ sk_A)
% 0.70/0.92         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.70/0.92         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['6', '32'])).
% 0.70/0.92  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('35', plain, ((v1_tdlat_3 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('37', plain,
% 0.70/0.92      ((((v2_struct_0 @ sk_A) | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.70/0.92         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.70/0.92  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('39', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('clc', [status(thm)], ['37', '38'])).
% 0.70/0.92  thf('40', plain,
% 0.70/0.92      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('split', [status(esa)], ['0'])).
% 0.70/0.92  thf('41', plain,
% 0.70/0.92      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.70/0.92         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.70/0.92             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['39', '40'])).
% 0.70/0.92  thf(fc14_subset_1, axiom,
% 0.70/0.92    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.70/0.92  thf('42', plain, (![X10 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X10) @ X10)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.70/0.92  thf('43', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.70/0.92  thf('44', plain, (![X10 : $i]: ~ (v1_subset_1 @ X10 @ X10)),
% 0.70/0.92      inference('demod', [status(thm)], ['42', '43'])).
% 0.70/0.92  thf('45', plain,
% 0.70/0.92      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.70/0.92       ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['41', '44'])).
% 0.70/0.92  thf('46', plain,
% 0.70/0.92      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.70/0.92       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('split', [status(esa)], ['8'])).
% 0.70/0.92  thf('47', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(d7_subset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.92       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.70/0.92  thf('48', plain,
% 0.70/0.92      (![X20 : $i, X21 : $i]:
% 0.70/0.92         (((X21) = (X20))
% 0.70/0.92          | (v1_subset_1 @ X21 @ X20)
% 0.70/0.92          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.70/0.92      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.70/0.92  thf('49', plain,
% 0.70/0.92      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.70/0.92        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['47', '48'])).
% 0.70/0.92  thf('50', plain,
% 0.70/0.92      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('split', [status(esa)], ['8'])).
% 0.70/0.92  thf('51', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('52', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(t48_tex_2, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.70/0.92             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.70/0.92  thf('53', plain,
% 0.70/0.92      (![X29 : $i, X30 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.70/0.92          | (v3_tex_2 @ X29 @ X30)
% 0.70/0.92          | ~ (v2_tex_2 @ X29 @ X30)
% 0.70/0.92          | ~ (v1_tops_1 @ X29 @ X30)
% 0.70/0.92          | ~ (l1_pre_topc @ X30)
% 0.70/0.92          | ~ (v2_pre_topc @ X30)
% 0.70/0.92          | (v2_struct_0 @ X30))),
% 0.70/0.92      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.70/0.92  thf('54', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((v2_struct_0 @ X0)
% 0.70/0.92          | ~ (v2_pre_topc @ X0)
% 0.70/0.92          | ~ (l1_pre_topc @ X0)
% 0.70/0.92          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.92          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.92          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['52', '53'])).
% 0.70/0.92  thf('55', plain,
% 0.70/0.92      (((~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.70/0.92         | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.70/0.92         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.70/0.92         | ~ (l1_pre_topc @ sk_A)
% 0.70/0.92         | ~ (v2_pre_topc @ sk_A)
% 0.70/0.92         | (v2_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['51', '54'])).
% 0.70/0.92  thf('56', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('57', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(d3_tops_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( l1_pre_topc @ A ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( ( v1_tops_1 @ B @ A ) <=>
% 0.70/0.92             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.70/0.92  thf('58', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.70/0.92          | ((k2_pre_topc @ X16 @ X15) != (k2_struct_0 @ X16))
% 0.70/0.92          | (v1_tops_1 @ X15 @ X16)
% 0.70/0.92          | ~ (l1_pre_topc @ X16))),
% 0.70/0.92      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.70/0.92  thf('59', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (l1_pre_topc @ X0)
% 0.70/0.92          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.92          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.92  thf('60', plain,
% 0.70/0.92      (((((k2_pre_topc @ sk_A @ sk_B_1) != (k2_struct_0 @ sk_A))
% 0.70/0.92         | (v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.70/0.92         | ~ (l1_pre_topc @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['56', '59'])).
% 0.70/0.92  thf(d3_struct_0, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.70/0.92  thf('61', plain,
% 0.70/0.92      (![X11 : $i]:
% 0.70/0.92         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.70/0.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.70/0.92  thf('62', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('63', plain,
% 0.70/0.92      (((((sk_B_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['61', '62'])).
% 0.70/0.92  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(dt_l1_pre_topc, axiom,
% 0.70/0.92    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.70/0.92  thf('65', plain,
% 0.70/0.92      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.70/0.92  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.92      inference('sup-', [status(thm)], ['64', '65'])).
% 0.70/0.92  thf('67', plain,
% 0.70/0.92      ((((sk_B_1) = (k2_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('demod', [status(thm)], ['63', '66'])).
% 0.70/0.92  thf('68', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('70', plain,
% 0.70/0.92      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.70/0.92         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('demod', [status(thm)], ['60', '67', '68', '69'])).
% 0.70/0.92  thf('71', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('72', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(dt_k3_subset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.92       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.70/0.92  thf('73', plain,
% 0.70/0.92      (![X2 : $i, X3 : $i]:
% 0.70/0.92         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.70/0.92          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.70/0.92  thf('74', plain,
% 0.70/0.92      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['72', '73'])).
% 0.70/0.92  thf(t17_tdlat_3, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.92       ( ( v1_tdlat_3 @ A ) <=>
% 0.70/0.92         ( ![B:$i]:
% 0.70/0.92           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.70/0.92  thf('75', plain,
% 0.70/0.92      (![X25 : $i, X26 : $i]:
% 0.70/0.92         (~ (v1_tdlat_3 @ X25)
% 0.70/0.92          | (v3_pre_topc @ X26 @ X25)
% 0.70/0.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.70/0.92          | ~ (l1_pre_topc @ X25)
% 0.70/0.92          | ~ (v2_pre_topc @ X25))),
% 0.70/0.92      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.70/0.92  thf('76', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v2_pre_topc @ X0)
% 0.70/0.92          | ~ (l1_pre_topc @ X0)
% 0.70/0.92          | (v3_pre_topc @ 
% 0.70/0.92             (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 0.70/0.92          | ~ (v1_tdlat_3 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['74', '75'])).
% 0.70/0.92  thf('77', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.70/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.92  thf(t29_tops_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( l1_pre_topc @ A ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( ( v4_pre_topc @ B @ A ) <=>
% 0.70/0.92             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.70/0.92  thf('78', plain,
% 0.70/0.92      (![X17 : $i, X18 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.70/0.92          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.70/0.92          | (v4_pre_topc @ X17 @ X18)
% 0.70/0.92          | ~ (l1_pre_topc @ X18))),
% 0.70/0.92      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.70/0.92  thf('79', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (l1_pre_topc @ X0)
% 0.70/0.92          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.92          | ~ (v3_pre_topc @ 
% 0.70/0.92               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['77', '78'])).
% 0.70/0.92  thf('80', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_tdlat_3 @ X0)
% 0.70/0.92          | ~ (l1_pre_topc @ X0)
% 0.70/0.92          | ~ (v2_pre_topc @ X0)
% 0.70/0.92          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.92          | ~ (l1_pre_topc @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['76', '79'])).
% 0.70/0.92  thf('81', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.92          | ~ (v2_pre_topc @ X0)
% 0.70/0.92          | ~ (l1_pre_topc @ X0)
% 0.70/0.92          | ~ (v1_tdlat_3 @ X0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['80'])).
% 0.70/0.92  thf('82', plain,
% 0.70/0.92      ((((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.70/0.92         | ~ (v1_tdlat_3 @ sk_A)
% 0.70/0.92         | ~ (l1_pre_topc @ sk_A)
% 0.70/0.92         | ~ (v2_pre_topc @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['71', '81'])).
% 0.70/0.92  thf('83', plain, ((v1_tdlat_3 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('86', plain,
% 0.70/0.92      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.70/0.92  thf('87', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(t52_pre_topc, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( l1_pre_topc @ A ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.92           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.70/0.92             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.70/0.92               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.70/0.92  thf('88', plain,
% 0.70/0.92      (![X13 : $i, X14 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.70/0.92          | ~ (v4_pre_topc @ X13 @ X14)
% 0.70/0.92          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.70/0.92          | ~ (l1_pre_topc @ X14))),
% 0.70/0.92      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.70/0.92  thf('89', plain,
% 0.70/0.92      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.92        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.70/0.92        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['87', '88'])).
% 0.70/0.92  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('91', plain,
% 0.70/0.92      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.70/0.92        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('demod', [status(thm)], ['89', '90'])).
% 0.70/0.92  thf('92', plain,
% 0.70/0.92      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['86', '91'])).
% 0.70/0.92  thf('93', plain,
% 0.70/0.92      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('demod', [status(thm)], ['70', '92'])).
% 0.70/0.92  thf('94', plain,
% 0.70/0.92      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('simplify', [status(thm)], ['93'])).
% 0.70/0.92  thf('95', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('96', plain,
% 0.70/0.92      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('97', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('98', plain,
% 0.70/0.92      (![X27 : $i, X28 : $i]:
% 0.70/0.92         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.70/0.92          | (v2_tex_2 @ X27 @ X28)
% 0.70/0.92          | ~ (l1_pre_topc @ X28)
% 0.70/0.92          | ~ (v1_tdlat_3 @ X28)
% 0.70/0.92          | ~ (v2_pre_topc @ X28)
% 0.70/0.92          | (v2_struct_0 @ X28))),
% 0.70/0.92      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.70/0.92  thf('99', plain,
% 0.70/0.92      (((v2_struct_0 @ sk_A)
% 0.70/0.92        | ~ (v2_pre_topc @ sk_A)
% 0.70/0.92        | ~ (v1_tdlat_3 @ sk_A)
% 0.70/0.92        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.92        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['97', '98'])).
% 0.70/0.92  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('101', plain, ((v1_tdlat_3 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('103', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.70/0.92  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('105', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.70/0.92      inference('clc', [status(thm)], ['103', '104'])).
% 0.70/0.92  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('108', plain,
% 0.70/0.92      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('demod', [status(thm)],
% 0.70/0.92                ['55', '94', '95', '96', '105', '106', '107'])).
% 0.70/0.92  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('110', plain,
% 0.70/0.92      (((v3_tex_2 @ sk_B_1 @ sk_A))
% 0.70/0.92         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.92      inference('clc', [status(thm)], ['108', '109'])).
% 0.70/0.92  thf('111', plain,
% 0.70/0.92      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.70/0.92      inference('split', [status(esa)], ['0'])).
% 0.70/0.92  thf('112', plain,
% 0.70/0.92      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.70/0.92       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['110', '111'])).
% 0.70/0.92  thf('113', plain, ($false),
% 0.70/0.92      inference('sat_resolution*', [status(thm)], ['1', '45', '46', '112'])).
% 0.70/0.92  
% 0.70/0.92  % SZS output end Refutation
% 0.70/0.92  
% 0.76/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
