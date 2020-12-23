%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y9A2zwmuCN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 258 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          : 1074 (4547 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t106_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( v4_pre_topc @ D @ B )
                        & ( v4_tops_1 @ D @ B ) )
                     => ( v5_tops_1 @ D @ B ) )
                    & ( ( v5_tops_1 @ C @ A )
                     => ( ( v4_pre_topc @ C @ A )
                        & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( v4_pre_topc @ D @ B )
                          & ( v4_tops_1 @ D @ B ) )
                       => ( v5_tops_1 @ D @ B ) )
                      & ( ( v5_tops_1 @ C @ A )
                       => ( ( v4_pre_topc @ C @ A )
                          & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tops_1])).

thf('0',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v5_tops_1 @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v5_tops_1 @ X10 @ X11 )
      | ( X10
        = ( k2_pre_topc @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X9 @ ( k2_pre_topc @ X9 @ X8 ) ) @ X8 )
      | ~ ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ ( k1_tops_1 @ X9 @ X8 ) ) )
      | ( v4_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_C )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('28',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','38','43'])).

thf('45',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('49',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
   <= ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('52',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('53',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['55'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ ( k2_pre_topc @ X4 @ X3 ) @ ( k2_pre_topc @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ ( k2_pre_topc @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ ( k2_pre_topc @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D )
    | ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['63','80'])).

thf('82',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_tops_1 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ ( k1_tops_1 @ X9 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
        = sk_D ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
      = sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X10
       != ( k2_pre_topc @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ( v5_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( sk_D != sk_D )
      | ( v5_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
   <= ~ ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['45'])).

thf('100',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','47','50','51','52','54','56','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y9A2zwmuCN
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 136 iterations in 0.069s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(t106_tops_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_pre_topc @ B ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                   ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.21/0.52                       ( v5_tops_1 @ D @ B ) ) & 
% 0.21/0.52                     ( ( v5_tops_1 @ C @ A ) =>
% 0.21/0.52                       ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( l1_pre_topc @ B ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                      ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.21/0.52                          ( v5_tops_1 @ D @ B ) ) & 
% 0.21/0.52                        ( ( v5_tops_1 @ C @ A ) =>
% 0.21/0.52                          ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t106_tops_1])).
% 0.21/0.52  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain, (((v4_pre_topc @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('4', plain, ((~ (v5_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((v5_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d7_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v5_tops_1 @ B @ A ) <=>
% 0.21/0.52             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | ~ (v5_tops_1 @ X10 @ X11)
% 0.21/0.52          | ((X10) = (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 0.21/0.52          | ~ (l1_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d6_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v4_tops_1 @ B @ A ) <=>
% 0.21/0.52             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.21/0.52               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | ~ (r1_tarski @ (k1_tops_1 @ X9 @ (k2_pre_topc @ X9 @ X8)) @ X8)
% 0.21/0.52          | ~ (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ (k1_tops_1 @ X9 @ X8)))
% 0.21/0.52          | (v4_tops_1 @ X8 @ X9)
% 0.21/0.52          | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v4_tops_1 @ sk_C @ sk_A)
% 0.21/0.52        | ~ (r1_tarski @ sk_C @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.21/0.52             sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_C @ sk_A)
% 0.21/0.52        | ~ (r1_tarski @ sk_C @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.21/0.52             sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((~ (r1_tarski @ sk_C @ sk_C)
% 0.21/0.52         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.21/0.52              sk_C)
% 0.21/0.52         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_C)
% 0.21/0.52         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k1_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X12)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.52          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf(fc1_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X14)
% 0.21/0.52          | ~ (v2_pre_topc @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | (v4_pre_topc @ (k2_pre_topc @ X14 @ X15) @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t52_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.52          | ~ (v4_pre_topc @ X6 @ X7)
% 0.21/0.52          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.21/0.52          | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_C) = (sk_C)) | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_C) = (sk_C)))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t44_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.52          | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '38', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((~ (v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.52        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '31'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((~ (v4_pre_topc @ sk_C @ sk_A)) <= (~ ((v4_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['45'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['4'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.52       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['45'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.52        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.52       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.52        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.52       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['55'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.52          | ~ (v4_pre_topc @ X6 @ X7)
% 0.21/0.52          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.21/0.52          | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | ((k2_pre_topc @ sk_B @ sk_D) = (sk_D))
% 0.21/0.52        | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_B @ sk_D) = (sk_D)) | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_B @ sk_D) = (sk_D)))
% 0.21/0.52         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X12)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.52          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf(t49_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ( r1_tarski @ B @ C ) =>
% 0.21/0.52                 ( r1_tarski @
% 0.21/0.52                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.52          | ~ (r1_tarski @ X3 @ X5)
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ X4 @ X3) @ (k2_pre_topc @ X4 @ X5))
% 0.21/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.52          | ~ (l1_pre_topc @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ 
% 0.21/0.52             (k2_pre_topc @ sk_B @ X0))
% 0.21/0.52          | ~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.52  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ 
% 0.21/0.52             (k2_pre_topc @ sk_B @ X0))
% 0.21/0.52          | ~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)
% 0.21/0.52        | (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ 
% 0.21/0.52           (k2_pre_topc @ sk_B @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.52          | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B) | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain, ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      ((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ 
% 0.21/0.52        (k2_pre_topc @ sk_B @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['74', '79'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D))
% 0.21/0.52         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['63', '80'])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['53'])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | ~ (v4_tops_1 @ X8 @ X9)
% 0.21/0.52          | (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ (k1_tops_1 @ X9 @ X8)))
% 0.21/0.52          | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.21/0.52        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.21/0.52        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['82', '87'])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (((~ (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.21/0.52         | ((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D))))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D)))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['81', '90'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | ((X10) != (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 0.21/0.52          | (v5_tops_1 @ X10 @ X11)
% 0.21/0.52          | ~ (l1_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | (v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.52  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (((v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.21/0.52      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      (((((sk_D) != (sk_D)) | (v5_tops_1 @ sk_D @ sk_B)))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['91', '96'])).
% 0.21/0.52  thf('98', plain,
% 0.21/0.52      (((v5_tops_1 @ sk_D @ sk_B))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['97'])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      ((~ (v5_tops_1 @ sk_D @ sk_B)) <= (~ ((v5_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['45'])).
% 0.21/0.52  thf('100', plain,
% 0.21/0.52      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_D @ sk_B)) | 
% 0.21/0.52       ((v5_tops_1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.52  thf('101', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)],
% 0.21/0.52                ['1', '3', '47', '50', '51', '52', '54', '56', '100'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
