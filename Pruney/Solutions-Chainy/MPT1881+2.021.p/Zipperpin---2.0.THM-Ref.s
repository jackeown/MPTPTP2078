%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EVUo1wVgiy

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 388 expanded)
%              Number of leaves         :   35 ( 123 expanded)
%              Depth                    :   16
%              Number of atoms          :  968 (4172 expanded)
%              Number of equality atoms :   37 (  90 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( v1_subset_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('9',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('14',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != ( u1_struct_0 @ X16 ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B )
       != sk_B )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('23',plain,
    ( ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( v1_subset_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('29',plain,
    ( ( ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      | ( ( k2_struct_0 @ sk_A )
        = sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X12: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('32',plain,
    ( ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('34',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','34'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X13: $i] :
      ( ( ( k2_pre_topc @ X13 @ ( k2_struct_0 @ X13 ) )
        = ( k2_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('37',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','34'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','40'])).

thf('42',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('44',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','42','43','44','53','54','55'])).

thf('57',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('62',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('72',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['85','87'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('89',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('90',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('91',plain,(
    ! [X9: $i] :
      ~ ( v1_subset_1 @ X9 @ X9 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['57','92'])).

thf('94',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['56','93'])).

thf('95',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['86'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['86'])).

thf('97',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','92','96'])).

thf('98',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['94','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EVUo1wVgiy
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 240 iterations in 0.115s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.57  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.57  thf(t49_tex_2, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.57         ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.57             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57              ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.57                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.21/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d7_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i]:
% 0.21/0.57         (((X18) = (X17))
% 0.21/0.57          | (v1_subset_1 @ X18 @ X17)
% 0.21/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf(dt_k2_subset_1, axiom,
% 0.21/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.57  thf('8', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.57  thf('9', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf(t48_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.57             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.57          | (v3_tex_2 @ X24 @ X25)
% 0.21/0.57          | ~ (v2_tex_2 @ X24 @ X25)
% 0.21/0.57          | ~ (v1_tops_1 @ X24 @ X25)
% 0.21/0.57          | ~ (l1_pre_topc @ X25)
% 0.21/0.57          | ~ (v2_pre_topc @ X25)
% 0.21/0.57          | (v2_struct_0 @ X25))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (((~ (v1_tops_1 @ sk_B @ sk_A)
% 0.21/0.57         | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57         | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.57  thf('13', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf(d2_tops_3, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.57             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X15 : $i, X16 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.57          | ((k2_pre_topc @ X16 @ X15) != (u1_struct_0 @ X16))
% 0.21/0.57          | (v1_tops_1 @ X15 @ X16)
% 0.21/0.57          | ~ (l1_pre_topc @ X16))),
% 0.21/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.57           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57           | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.57           | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) != (sk_B))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | (v1_tops_1 @ sk_B @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf(dt_k2_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) =>
% 0.21/0.57       ( m1_subset_1 @
% 0.21/0.57         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X10 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_struct_0 @ X10) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.57          | ~ (l1_struct_0 @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      ((((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_l1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.57  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['23', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i]:
% 0.21/0.57         (((X18) = (X17))
% 0.21/0.57          | (v1_subset_1 @ X18 @ X17)
% 0.21/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((((v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.57         | ((k2_struct_0 @ sk_A) = (sk_B))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf(fc12_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) =>
% 0.21/0.57       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X12 : $i]:
% 0.21/0.57         (~ (v1_subset_1 @ (k2_struct_0 @ X12) @ (u1_struct_0 @ X12))
% 0.21/0.57          | ~ (l1_struct_0 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (sk_B)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('clc', [status(thm)], ['29', '34'])).
% 0.21/0.57  thf(t27_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X13 : $i]:
% 0.21/0.57         (((k2_pre_topc @ X13 @ (k2_struct_0 @ X13)) = (k2_struct_0 @ X13))
% 0.21/0.57          | ~ (l1_pre_topc @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (sk_B)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('clc', [status(thm)], ['29', '34'])).
% 0.21/0.57  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((((sk_B) != (sk_B)) | (v1_tops_1 @ sk_B @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (((v1_tops_1 @ sk_B @ sk_A))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t43_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.57         ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | (v2_tex_2 @ X22 @ X23)
% 0.21/0.57          | ~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (v1_tdlat_3 @ X23)
% 0.21/0.57          | ~ (v2_pre_topc @ X23)
% 0.21/0.57          | (v2_struct_0 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.57  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('49', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('51', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.21/0.57  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('53', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.57      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      ((((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)],
% 0.21/0.57                ['12', '42', '43', '44', '53', '54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.57       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['4'])).
% 0.21/0.57  thf('58', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | (v2_tex_2 @ X22 @ X23)
% 0.21/0.57          | ~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (v1_tdlat_3 @ X23)
% 0.21/0.57          | ~ (v2_pre_topc @ X23)
% 0.21/0.57          | (v2_struct_0 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.57  thf('61', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['4'])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d7_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.57             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.57               ( ![C:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.57                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.57          | ~ (v3_tex_2 @ X19 @ X20)
% 0.21/0.57          | ~ (v2_tex_2 @ X21 @ X20)
% 0.21/0.57          | ~ (r1_tarski @ X19 @ X21)
% 0.21/0.57          | ((X19) = (X21))
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.57          | ~ (l1_pre_topc @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ((sk_B) = (X0))
% 0.21/0.57          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.57          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.57          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.57  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ((sk_B) = (X0))
% 0.21/0.57          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.57          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.57          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.57           | ((sk_B) = (X0))
% 0.21/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['62', '67'])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.57         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '68'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(l3_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.57          | (r2_hidden @ X6 @ X8)
% 0.21/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_tarski @ sk_B @ X0)
% 0.21/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.57  thf('77', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.57         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['69', '77'])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57         | (v2_struct_0 @ sk_A)
% 0.21/0.57         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['60', '78'])).
% 0.21/0.57  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('81', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.21/0.57  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('clc', [status(thm)], ['83', '84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['86'])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B @ sk_B))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['85', '87'])).
% 0.21/0.57  thf(fc14_subset_1, axiom,
% 0.21/0.57    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.21/0.57  thf('89', plain, (![X9 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X9) @ X9)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.21/0.57  thf('90', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.57  thf('91', plain, (![X9 : $i]: ~ (v1_subset_1 @ X9 @ X9)),
% 0.21/0.57      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.21/0.57       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['88', '91'])).
% 0.21/0.57  thf('93', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['57', '92'])).
% 0.21/0.57  thf('94', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['56', '93'])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['86'])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.21/0.57       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['86'])).
% 0.21/0.57  thf('97', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['57', '92', '96'])).
% 0.21/0.57  thf('98', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 0.21/0.57  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('clc', [status(thm)], ['94', '98'])).
% 0.21/0.57  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
