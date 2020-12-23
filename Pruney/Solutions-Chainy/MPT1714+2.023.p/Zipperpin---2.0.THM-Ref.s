%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZogL8zHGQs

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 851 expanded)
%              Number of leaves         :   26 ( 255 expanded)
%              Depth                    :   29
%              Number of atoms          : 1058 (11541 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t23_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) )
                      | ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) )
                        | ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tmap_1])).

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('9',plain,
    ( ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C_2 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C_2 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_C_2 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('25',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['13','14'])).

thf('44',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('57',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('66',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('72',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('74',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('93',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('95',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('98',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,
    ( ~ ( r1_tsep_1 @ sk_C_2 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['102'])).

thf('107',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['102'])).

thf('109',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_2 )
    | ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('110',plain,(
    r1_tsep_1 @ sk_D @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['104','107','108','109'])).

thf('111',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['57','110'])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('114',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['102'])).

thf('116',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('118',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('120',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('122',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('125',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['116','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('128',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['102'])).

thf('130',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['104','107','109','130','108'])).

thf('132',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['115','131'])).

thf('133',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['114','132'])).

thf('134',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['87','88'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZogL8zHGQs
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:17:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 134 iterations in 0.058s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(dt_l1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.50  thf('0', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('1', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('2', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('3', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('4', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('5', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf(t23_tmap_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.50               ( ![D:$i]:
% 0.19/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.50                   ( ( m1_pre_topc @ B @ C ) =>
% 0.19/0.50                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.19/0.50                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.19/0.50                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.50            ( l1_pre_topc @ A ) ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.50                  ( ![D:$i]:
% 0.19/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.50                      ( ( m1_pre_topc @ B @ C ) =>
% 0.19/0.50                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.19/0.50                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.19/0.50                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C_2))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_D @ sk_C_2)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('split', [status(esa)], ['6'])).
% 0.19/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.19/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X16)
% 0.19/0.50          | ~ (l1_struct_0 @ X17)
% 0.19/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.19/0.50          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.19/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      ((((r1_tsep_1 @ sk_C_2 @ sk_D)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_C_2)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_C_2)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_tsep_1 @ sk_C_2 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '9'])).
% 0.19/0.50  thf('11', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_m1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.50          | (l1_pre_topc @ X12)
% 0.19/0.50          | ~ (l1_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.50  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain, ((l1_pre_topc @ sk_C_2)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_C_2 @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '15'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_C_2 @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '16'])).
% 0.19/0.50  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.50          | (l1_pre_topc @ X12)
% 0.19/0.50          | ~ (l1_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.50  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('22', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '22'])).
% 0.19/0.50  thf(d3_tsep_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_struct_0 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( l1_struct_0 @ B ) =>
% 0.19/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.19/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X14)
% 0.19/0.50          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.19/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.19/0.50          | ~ (l1_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_C_2)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_C_2)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '25'])).
% 0.19/0.50  thf('27', plain, ((l1_pre_topc @ sk_C_2)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '28'])).
% 0.19/0.50  thf('30', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf(t3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X6 @ X4)
% 0.19/0.50          | ~ (r2_hidden @ X6 @ X7)
% 0.19/0.50          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.50          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.50          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.19/0.50          | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['32', '35'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['31', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_C_2)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t1_tsep_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_pre_topc @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.50           ( m1_subset_1 @
% 0.19/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X18 @ X19)
% 0.19/0.50          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.19/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.50          | ~ (l1_pre_topc @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_C_2)
% 0.19/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain, ((l1_pre_topc @ sk_C_2)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf(t3_subset, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (![X8 : $i, X9 : $i]:
% 0.19/0.50         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.50          | (r2_hidden @ X0 @ X2)
% 0.19/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | (r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ X0) @ 
% 0.19/0.50             (u1_struct_0 @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['39', '48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X6 @ X4)
% 0.19/0.50          | ~ (r2_hidden @ X6 @ X7)
% 0.19/0.50          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.50          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.50          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['49', '52'])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['38', '54'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X14)
% 0.19/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.19/0.50          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.50          | ~ (l1_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_D)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('split', [status(esa)], ['6'])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X14)
% 0.19/0.50          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.19/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.19/0.50          | ~ (l1_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_C_2)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_C_2)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['63', '66'])).
% 0.19/0.50  thf('68', plain, ((l1_pre_topc @ sk_C_2)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('69', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.19/0.50  thf('70', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D))))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['62', '69'])).
% 0.19/0.50  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('72', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.50  thf('73', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.50  thf('74', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.50  thf('75', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('76', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.50  thf('77', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 0.19/0.50             (u1_struct_0 @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.19/0.50  thf('78', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.50          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('79', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.19/0.50          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.19/0.50  thf('80', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['79'])).
% 0.19/0.50  thf('81', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['74', '80'])).
% 0.19/0.50  thf('82', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X14)
% 0.19/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.19/0.50          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.50          | ~ (l1_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.50  thf('83', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.19/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.19/0.50  thf('84', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['61', '83'])).
% 0.19/0.50  thf('85', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('86', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.50          | (l1_pre_topc @ X12)
% 0.19/0.50          | ~ (l1_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.50  thf('87', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['85', '86'])).
% 0.19/0.50  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('90', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['84', '89'])).
% 0.19/0.50  thf('91', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['60', '90'])).
% 0.19/0.50  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('93', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['91', '92'])).
% 0.19/0.50  thf('94', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X16)
% 0.19/0.50          | ~ (l1_struct_0 @ X17)
% 0.19/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.19/0.50          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.19/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.50  thf('95', plain,
% 0.19/0.50      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.19/0.50  thf('96', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.50         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['59', '95'])).
% 0.19/0.50  thf('97', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('98', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['96', '97'])).
% 0.19/0.50  thf('99', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['58', '98'])).
% 0.19/0.50  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('101', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['99', '100'])).
% 0.19/0.50  thf('102', plain,
% 0.19/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('103', plain,
% 0.19/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['102'])).
% 0.19/0.50  thf('104', plain,
% 0.19/0.50      (~ ((r1_tsep_1 @ sk_C_2 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['101', '103'])).
% 0.19/0.50  thf('105', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['91', '92'])).
% 0.19/0.50  thf('106', plain,
% 0.19/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.19/0.50      inference('split', [status(esa)], ['102'])).
% 0.19/0.50  thf('107', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C_2 @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['105', '106'])).
% 0.19/0.50  thf('108', plain,
% 0.19/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.50      inference('split', [status(esa)], ['102'])).
% 0.19/0.50  thf('109', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_D @ sk_C_2)) | ((r1_tsep_1 @ sk_C_2 @ sk_D))),
% 0.19/0.50      inference('split', [status(esa)], ['6'])).
% 0.19/0.50  thf('110', plain, (((r1_tsep_1 @ sk_D @ sk_C_2))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['104', '107', '108', '109'])).
% 0.19/0.50  thf('111', plain,
% 0.19/0.50      ((~ (l1_struct_0 @ sk_D)
% 0.19/0.50        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.50        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['57', '110'])).
% 0.19/0.50  thf('112', plain,
% 0.19/0.50      ((~ (l1_pre_topc @ sk_D)
% 0.19/0.50        | ~ (l1_struct_0 @ sk_B)
% 0.19/0.50        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '111'])).
% 0.19/0.50  thf('113', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('114', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['112', '113'])).
% 0.19/0.50  thf('115', plain,
% 0.19/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['102'])).
% 0.19/0.50  thf('116', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('117', plain,
% 0.19/0.50      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('118', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['31', '37'])).
% 0.19/0.50  thf('119', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.19/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['79'])).
% 0.19/0.50  thf('120', plain,
% 0.19/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['118', '119'])).
% 0.19/0.50  thf('121', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (l1_struct_0 @ X14)
% 0.19/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.19/0.50          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.50          | ~ (l1_struct_0 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.50  thf('122', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.19/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['120', '121'])).
% 0.19/0.50  thf('123', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.19/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['117', '122'])).
% 0.19/0.50  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('125', plain,
% 0.19/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['123', '124'])).
% 0.19/0.50  thf('126', plain,
% 0.19/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['116', '125'])).
% 0.19/0.50  thf('127', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('128', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.19/0.50      inference('demod', [status(thm)], ['126', '127'])).
% 0.19/0.50  thf('129', plain,
% 0.19/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.19/0.50      inference('split', [status(esa)], ['102'])).
% 0.19/0.50  thf('130', plain,
% 0.19/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C_2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['128', '129'])).
% 0.19/0.50  thf('131', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)],
% 0.19/0.50                ['104', '107', '109', '130', '108'])).
% 0.19/0.50  thf('132', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['115', '131'])).
% 0.19/0.50  thf('133', plain, (~ (l1_struct_0 @ sk_B)),
% 0.19/0.50      inference('clc', [status(thm)], ['114', '132'])).
% 0.19/0.50  thf('134', plain, (~ (l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '133'])).
% 0.19/0.50  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('136', plain, ($false), inference('demod', [status(thm)], ['134', '135'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
