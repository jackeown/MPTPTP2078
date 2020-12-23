%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yymovaaWdc

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:13 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 317 expanded)
%              Number of leaves         :   31 ( 101 expanded)
%              Depth                    :   17
%              Number of atoms          :  944 (3506 expanded)
%              Number of equality atoms :   37 (  76 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( v1_subset_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('4',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( v1_tops_1 @ sk_B @ sk_A )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('15',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != ( u1_struct_0 @ X16 ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B )
       != sk_B )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ X12 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_tops_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','42'])).

thf('44',plain,
    ( ( v1_tops_1 @ sk_B @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('46',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','44','45','46','55','56','57'])).

thf('59',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('60',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('64',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('85',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('86',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('87',plain,(
    ! [X6: $i] :
      ~ ( v1_subset_1 @ X6 @ X6 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['59','88'])).

thf('90',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['58','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( $false
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','92'])).

thf('94',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['59','88','94'])).

thf('96',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['93','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yymovaaWdc
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 240 iterations in 0.135s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.59  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.36/0.59  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.36/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.36/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.59  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(t49_tex_2, conjecture,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.36/0.59         ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( ( v3_tex_2 @ B @ A ) <=>
% 0.36/0.59             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i]:
% 0.36/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.59            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59          ( ![B:$i]:
% 0.36/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59              ( ( v3_tex_2 @ B @ A ) <=>
% 0.36/0.59                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['0'])).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d7_subset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.59       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X17 : $i, X18 : $i]:
% 0.36/0.59         (((X18) = (X17))
% 0.36/0.59          | (v1_subset_1 @ X18 @ X17)
% 0.36/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('split', [status(esa)], ['5'])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.59  thf(dt_k2_subset_1, axiom,
% 0.36/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.59  thf('9', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.36/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.59  thf('10', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf(t48_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.36/0.59             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X24 : $i, X25 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.36/0.59          | (v3_tex_2 @ X24 @ X25)
% 0.36/0.59          | ~ (v2_tex_2 @ X24 @ X25)
% 0.36/0.59          | ~ (v1_tops_1 @ X24 @ X25)
% 0.36/0.59          | ~ (l1_pre_topc @ X25)
% 0.36/0.59          | ~ (v2_pre_topc @ X25)
% 0.36/0.59          | (v2_struct_0 @ X25))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v2_struct_0 @ X0)
% 0.36/0.59          | ~ (v2_pre_topc @ X0)
% 0.36/0.59          | ~ (l1_pre_topc @ X0)
% 0.36/0.59          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.59          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.59          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (((~ (v1_tops_1 @ sk_B @ sk_A)
% 0.36/0.59         | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.59         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59         | (v2_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['7', '12'])).
% 0.36/0.59  thf('14', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.59  thf(d2_tops_3, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_pre_topc @ A ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( ( v1_tops_1 @ B @ A ) <=>
% 0.36/0.59             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.59          | ((k2_pre_topc @ X16 @ X15) != (u1_struct_0 @ X16))
% 0.36/0.59          | (v1_tops_1 @ X15 @ X16)
% 0.36/0.59          | ~ (l1_pre_topc @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      ((![X0 : $i]:
% 0.36/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.36/0.59           | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59           | (v1_tops_1 @ X0 @ sk_A)
% 0.36/0.59           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.59  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      ((![X0 : $i]:
% 0.36/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.36/0.59           | (v1_tops_1 @ X0 @ sk_A)
% 0.36/0.59           | ((k2_pre_topc @ sk_A @ X0) != (sk_B))))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | (v1_tops_1 @ sk_B @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['14', '20'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t48_pre_topc, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_pre_topc @ A ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.59          | (r1_tarski @ X12 @ (k2_pre_topc @ X13 @ X12))
% 0.36/0.59          | ~ (l1_pre_topc @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.59  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('26', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf(t12_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]:
% 0.36/0.59         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.36/0.59         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(dt_k2_pre_topc, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59       ( m1_subset_1 @
% 0.36/0.59         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i]:
% 0.36/0.59         (~ (l1_pre_topc @ X10)
% 0.36/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.36/0.59          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 0.36/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.59  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup+', [status(thm)], ['29', '34'])).
% 0.36/0.59  thf(t3_subset, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X7 : $i, X8 : $i]:
% 0.36/0.59         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]:
% 0.36/0.59         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      ((((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      ((((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup+', [status(thm)], ['28', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      (((((sk_B) != (sk_B)) | (v1_tops_1 @ sk_B @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('demod', [status(thm)], ['21', '42'])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      (((v1_tops_1 @ sk_B @ sk_A))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t43_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.36/0.59         ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      (![X22 : $i, X23 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.59          | (v2_tex_2 @ X22 @ X23)
% 0.36/0.59          | ~ (l1_pre_topc @ X23)
% 0.36/0.59          | ~ (v1_tdlat_3 @ X23)
% 0.36/0.59          | ~ (v2_pre_topc @ X23)
% 0.36/0.59          | (v2_struct_0 @ X23))),
% 0.36/0.59      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v1_tdlat_3 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.59  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('51', plain, ((v1_tdlat_3 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('53', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.36/0.59  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('55', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['53', '54'])).
% 0.36/0.59  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('58', plain,
% 0.36/0.59      ((((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.36/0.59         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('demod', [status(thm)],
% 0.36/0.59                ['13', '44', '45', '46', '55', '56', '57'])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.36/0.59       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('split', [status(esa)], ['5'])).
% 0.36/0.59  thf('60', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf('61', plain,
% 0.36/0.59      (![X22 : $i, X23 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.59          | (v2_tex_2 @ X22 @ X23)
% 0.36/0.59          | ~ (l1_pre_topc @ X23)
% 0.36/0.59          | ~ (v1_tdlat_3 @ X23)
% 0.36/0.59          | ~ (v2_pre_topc @ X23)
% 0.36/0.59          | (v2_struct_0 @ X23))),
% 0.36/0.59      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.36/0.59  thf('62', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v2_struct_0 @ X0)
% 0.36/0.59          | ~ (v2_pre_topc @ X0)
% 0.36/0.59          | ~ (v1_tdlat_3 @ X0)
% 0.36/0.59          | ~ (l1_pre_topc @ X0)
% 0.36/0.59          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.59  thf('63', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf('64', plain,
% 0.36/0.59      (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['5'])).
% 0.36/0.59  thf('65', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d7_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_pre_topc @ A ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( ( v3_tex_2 @ B @ A ) <=>
% 0.36/0.59             ( ( v2_tex_2 @ B @ A ) & 
% 0.36/0.59               ( ![C:$i]:
% 0.36/0.59                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.59                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.59  thf('66', plain,
% 0.36/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.59          | ~ (v3_tex_2 @ X19 @ X20)
% 0.36/0.59          | ~ (v2_tex_2 @ X21 @ X20)
% 0.36/0.59          | ~ (r1_tarski @ X19 @ X21)
% 0.36/0.59          | ((X19) = (X21))
% 0.36/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.59          | ~ (l1_pre_topc @ X20))),
% 0.36/0.59      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.36/0.59  thf('67', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (l1_pre_topc @ sk_A)
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59          | ((sk_B) = (X0))
% 0.36/0.59          | ~ (r1_tarski @ sk_B @ X0)
% 0.36/0.59          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.59          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.59  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('69', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59          | ((sk_B) = (X0))
% 0.36/0.59          | ~ (r1_tarski @ sk_B @ X0)
% 0.36/0.59          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.59          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['67', '68'])).
% 0.36/0.59  thf('70', plain,
% 0.36/0.59      ((![X0 : $i]:
% 0.36/0.59          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.59           | ~ (r1_tarski @ sk_B @ X0)
% 0.36/0.59           | ((sk_B) = (X0))
% 0.36/0.59           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.36/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['64', '69'])).
% 0.36/0.59  thf('71', plain,
% 0.36/0.59      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.36/0.59         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.59         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.36/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['63', '70'])).
% 0.36/0.59  thf('72', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('73', plain,
% 0.36/0.59      (![X7 : $i, X8 : $i]:
% 0.36/0.59         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.59  thf('74', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.59  thf('75', plain,
% 0.36/0.59      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.36/0.59         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.36/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['71', '74'])).
% 0.36/0.59  thf('76', plain,
% 0.36/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.36/0.59         | ~ (v1_tdlat_3 @ sk_A)
% 0.36/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59         | (v2_struct_0 @ sk_A)
% 0.36/0.59         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['62', '75'])).
% 0.36/0.59  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('78', plain, ((v1_tdlat_3 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('80', plain,
% 0.36/0.59      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.36/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.36/0.59  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('82', plain,
% 0.36/0.59      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['80', '81'])).
% 0.36/0.59  thf('83', plain,
% 0.36/0.59      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.59         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('split', [status(esa)], ['0'])).
% 0.36/0.59  thf('84', plain,
% 0.36/0.59      (((v1_subset_1 @ sk_B @ sk_B))
% 0.36/0.59         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.36/0.59             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup+', [status(thm)], ['82', '83'])).
% 0.36/0.59  thf(fc14_subset_1, axiom,
% 0.36/0.59    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.36/0.59  thf('85', plain, (![X6 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X6) @ X6)),
% 0.36/0.59      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.36/0.59  thf('86', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.36/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.59  thf('87', plain, (![X6 : $i]: ~ (v1_subset_1 @ X6 @ X6)),
% 0.36/0.59      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.59  thf('88', plain,
% 0.36/0.59      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.36/0.59       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['84', '87'])).
% 0.36/0.59  thf('89', plain, (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['59', '88'])).
% 0.36/0.59  thf('90', plain, (((v3_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['58', '89'])).
% 0.36/0.59  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('92', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['90', '91'])).
% 0.36/0.59  thf('93', plain, (($false) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['1', '92'])).
% 0.36/0.59  thf('94', plain,
% 0.36/0.59      (~ ((v3_tex_2 @ sk_B @ sk_A)) | 
% 0.36/0.59       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['0'])).
% 0.36/0.59  thf('95', plain, (~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['59', '88', '94'])).
% 0.36/0.59  thf('96', plain, ($false),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['93', '95'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
