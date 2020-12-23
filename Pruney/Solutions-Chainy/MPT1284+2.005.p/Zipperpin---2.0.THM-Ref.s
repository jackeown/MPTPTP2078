%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5DpkCFtMWq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:54 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 290 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          : 1144 (5174 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v5_tops_1 @ X9 @ X10 )
      | ( X9
        = ( k2_pre_topc @ X10 @ ( k1_tops_1 @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ( v4_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('27',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['20','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_pre_topc @ X5 @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
        = X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( r1_tarski @ X3 @ ( k2_pre_topc @ X4 @ X3 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','19','37','44'])).

thf('46',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['20','30'])).

thf('50',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
   <= ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('51',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('54',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_pre_topc @ X5 @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
        = X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('80',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ( r1_tarski @ ( k2_pre_topc @ X16 @ X17 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_D )
        | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','85'])).

thf('87',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
        = sk_D ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
      = sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9
       != ( k2_pre_topc @ X10 @ ( k1_tops_1 @ X10 @ X9 ) ) )
      | ( v5_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( sk_D != sk_D )
      | ( v5_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
   <= ~ ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('105',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','48','51','52','53','55','57','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5DpkCFtMWq
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.60  % Solved by: fo/fo7.sh
% 0.35/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.60  % done 135 iterations in 0.098s
% 0.35/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.60  % SZS output start Refutation
% 0.35/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.60  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.35/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.60  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.35/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.60  thf(t106_tops_1, conjecture,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( l1_pre_topc @ B ) =>
% 0.35/0.60           ( ![C:$i]:
% 0.35/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60               ( ![D:$i]:
% 0.35/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.35/0.60                   ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.35/0.60                       ( v5_tops_1 @ D @ B ) ) & 
% 0.35/0.60                     ( ( v5_tops_1 @ C @ A ) =>
% 0.35/0.60                       ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.60    (~( ![A:$i]:
% 0.35/0.60        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.60          ( ![B:$i]:
% 0.35/0.60            ( ( l1_pre_topc @ B ) =>
% 0.35/0.60              ( ![C:$i]:
% 0.35/0.60                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60                  ( ![D:$i]:
% 0.35/0.60                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.35/0.60                      ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.35/0.60                          ( v5_tops_1 @ D @ B ) ) & 
% 0.35/0.60                        ( ( v5_tops_1 @ C @ A ) =>
% 0.35/0.60                          ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.60    inference('cnf.neg', [status(esa)], [t106_tops_1])).
% 0.35/0.60  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('split', [status(esa)], ['0'])).
% 0.35/0.60  thf('2', plain, (((v4_pre_topc @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('3', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('split', [status(esa)], ['2'])).
% 0.35/0.60  thf('4', plain, ((~ (v5_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('5', plain,
% 0.35/0.60      (((v5_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('split', [status(esa)], ['4'])).
% 0.35/0.60  thf('6', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(d7_tops_1, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_pre_topc @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60           ( ( v5_tops_1 @ B @ A ) <=>
% 0.35/0.60             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.60  thf('7', plain,
% 0.35/0.60      (![X9 : $i, X10 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.60          | ~ (v5_tops_1 @ X9 @ X10)
% 0.35/0.60          | ((X9) = (k2_pre_topc @ X10 @ (k1_tops_1 @ X10 @ X9)))
% 0.35/0.60          | ~ (l1_pre_topc @ X10))),
% 0.35/0.60      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.35/0.60  thf('8', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.60        | ((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.60        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.60  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('10', plain,
% 0.35/0.60      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.60        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.60  thf('11', plain,
% 0.35/0.60      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.60         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['5', '10'])).
% 0.35/0.60  thf('12', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(d6_tops_1, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_pre_topc @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60           ( ( v4_tops_1 @ B @ A ) <=>
% 0.35/0.60             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.35/0.60               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.35/0.60  thf('13', plain,
% 0.35/0.60      (![X7 : $i, X8 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.35/0.60          | ~ (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.35/0.60          | ~ (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.35/0.60          | (v4_tops_1 @ X7 @ X8)
% 0.35/0.60          | ~ (l1_pre_topc @ X8))),
% 0.35/0.60      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.35/0.60  thf('14', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.60        | (v4_tops_1 @ sk_C @ sk_A)
% 0.35/0.60        | ~ (r1_tarski @ sk_C @ 
% 0.35/0.60             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.60        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.35/0.60             sk_C))),
% 0.35/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.60  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('16', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_C @ sk_A)
% 0.35/0.60        | ~ (r1_tarski @ sk_C @ 
% 0.35/0.60             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.60        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.35/0.60             sk_C))),
% 0.35/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.60  thf('17', plain,
% 0.35/0.60      (((~ (r1_tarski @ sk_C @ sk_C)
% 0.35/0.60         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.35/0.60              sk_C)
% 0.35/0.60         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['11', '16'])).
% 0.35/0.60  thf(d10_xboole_0, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.60  thf('18', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.35/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.60  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.60  thf('20', plain,
% 0.35/0.60      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.60         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['5', '10'])).
% 0.35/0.60  thf('21', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(dt_k1_tops_1, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.60       ( m1_subset_1 @
% 0.35/0.60         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.60  thf('22', plain,
% 0.35/0.60      (![X11 : $i, X12 : $i]:
% 0.35/0.60         (~ (l1_pre_topc @ X11)
% 0.35/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.60          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 0.35/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.35/0.60      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.35/0.60  thf('23', plain,
% 0.35/0.60      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.60  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('25', plain,
% 0.35/0.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.60  thf(fc1_tops_1, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.60       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.35/0.60  thf('26', plain,
% 0.35/0.60      (![X13 : $i, X14 : $i]:
% 0.35/0.60         (~ (l1_pre_topc @ X13)
% 0.35/0.60          | ~ (v2_pre_topc @ X13)
% 0.35/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.60          | (v4_pre_topc @ (k2_pre_topc @ X13 @ X14) @ X13))),
% 0.35/0.60      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.35/0.60  thf('27', plain,
% 0.35/0.60      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)
% 0.35/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.60  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('30', plain,
% 0.35/0.60      ((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.35/0.60  thf('31', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup+', [status(thm)], ['20', '30'])).
% 0.35/0.60  thf('32', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(t52_pre_topc, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_pre_topc @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.35/0.60             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.35/0.60               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.35/0.60  thf('33', plain,
% 0.35/0.60      (![X5 : $i, X6 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.35/0.60          | ~ (v4_pre_topc @ X5 @ X6)
% 0.35/0.60          | ((k2_pre_topc @ X6 @ X5) = (X5))
% 0.35/0.60          | ~ (l1_pre_topc @ X6))),
% 0.35/0.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.35/0.60  thf('34', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.60        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.35/0.60        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.60  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('36', plain,
% 0.35/0.60      ((((k2_pre_topc @ sk_A @ sk_C) = (sk_C)) | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.60  thf('37', plain,
% 0.35/0.60      ((((k2_pre_topc @ sk_A @ sk_C) = (sk_C)))
% 0.35/0.60         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['31', '36'])).
% 0.35/0.60  thf('38', plain,
% 0.35/0.60      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.60         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['5', '10'])).
% 0.35/0.60  thf('39', plain,
% 0.35/0.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.60  thf(t48_pre_topc, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_pre_topc @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.35/0.60  thf('40', plain,
% 0.35/0.60      (![X3 : $i, X4 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.35/0.60          | (r1_tarski @ X3 @ (k2_pre_topc @ X4 @ X3))
% 0.35/0.60          | ~ (l1_pre_topc @ X4))),
% 0.35/0.60      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.35/0.60  thf('41', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.60        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.60           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.35/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.60  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('43', plain,
% 0.35/0.60      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.60        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.35/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.60  thf('44', plain,
% 0.35/0.60      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.35/0.60         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup+', [status(thm)], ['38', '43'])).
% 0.35/0.60  thf('45', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('demod', [status(thm)], ['17', '19', '37', '44'])).
% 0.35/0.60  thf('46', plain,
% 0.35/0.60      ((~ (v5_tops_1 @ sk_D @ sk_B)
% 0.35/0.60        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.35/0.60        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('47', plain,
% 0.35/0.60      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('split', [status(esa)], ['46'])).
% 0.35/0.60  thf('48', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['45', '47'])).
% 0.35/0.60  thf('49', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.35/0.60      inference('sup+', [status(thm)], ['20', '30'])).
% 0.35/0.60  thf('50', plain,
% 0.35/0.60      ((~ (v4_pre_topc @ sk_C @ sk_A)) <= (~ ((v4_pre_topc @ sk_C @ sk_A)))),
% 0.35/0.60      inference('split', [status(esa)], ['46'])).
% 0.35/0.60  thf('51', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.60  thf('52', plain,
% 0.35/0.60      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('split', [status(esa)], ['4'])).
% 0.35/0.60  thf('53', plain,
% 0.35/0.60      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.35/0.60       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('split', [status(esa)], ['46'])).
% 0.35/0.60  thf('54', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_D @ sk_B)
% 0.35/0.60        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.35/0.60        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('55', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.35/0.60       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('split', [status(esa)], ['54'])).
% 0.35/0.60  thf('56', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_D @ sk_B)
% 0.35/0.60        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.35/0.60        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('57', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.35/0.60       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.35/0.60      inference('split', [status(esa)], ['56'])).
% 0.35/0.60  thf('58', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_D @ sk_B)) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('split', [status(esa)], ['56'])).
% 0.35/0.60  thf('59', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('60', plain,
% 0.35/0.60      (![X5 : $i, X6 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.35/0.60          | ~ (v4_pre_topc @ X5 @ X6)
% 0.35/0.60          | ((k2_pre_topc @ X6 @ X5) = (X5))
% 0.35/0.60          | ~ (l1_pre_topc @ X6))),
% 0.35/0.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.35/0.60  thf('61', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.35/0.60        | ((k2_pre_topc @ sk_B @ sk_D) = (sk_D))
% 0.35/0.60        | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.60  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('63', plain,
% 0.35/0.60      ((((k2_pre_topc @ sk_B @ sk_D) = (sk_D)) | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.35/0.60      inference('demod', [status(thm)], ['61', '62'])).
% 0.35/0.60  thf('64', plain,
% 0.35/0.60      ((((k2_pre_topc @ sk_B @ sk_D) = (sk_D)))
% 0.35/0.60         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['58', '63'])).
% 0.35/0.60  thf('65', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.35/0.60      inference('split', [status(esa)], ['54'])).
% 0.35/0.60  thf('66', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('67', plain,
% 0.35/0.60      (![X7 : $i, X8 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.35/0.60          | ~ (v4_tops_1 @ X7 @ X8)
% 0.35/0.60          | (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.35/0.60          | ~ (l1_pre_topc @ X8))),
% 0.35/0.60      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.35/0.60  thf('68', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.35/0.60        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.35/0.60        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.35/0.60  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('70', plain,
% 0.35/0.60      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.35/0.60        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.35/0.60      inference('demod', [status(thm)], ['68', '69'])).
% 0.35/0.60  thf('71', plain,
% 0.35/0.60      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['65', '70'])).
% 0.35/0.60  thf('72', plain,
% 0.35/0.60      (((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup+', [status(thm)], ['64', '71'])).
% 0.35/0.60  thf('73', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('74', plain,
% 0.35/0.60      (![X11 : $i, X12 : $i]:
% 0.35/0.60         (~ (l1_pre_topc @ X11)
% 0.35/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.60          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 0.35/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.35/0.60      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.35/0.60  thf('75', plain,
% 0.35/0.60      (((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.35/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.35/0.60        | ~ (l1_pre_topc @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.35/0.60  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('77', plain,
% 0.35/0.60      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.35/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.35/0.60  thf('78', plain,
% 0.35/0.60      (((v4_pre_topc @ sk_D @ sk_B)) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('split', [status(esa)], ['56'])).
% 0.35/0.60  thf('79', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(t31_tops_1, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_pre_topc @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60           ( ![C:$i]:
% 0.35/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.35/0.60                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.35/0.60  thf('80', plain,
% 0.35/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.60          | ~ (v4_pre_topc @ X15 @ X16)
% 0.35/0.60          | ~ (r1_tarski @ X17 @ X15)
% 0.35/0.60          | (r1_tarski @ (k2_pre_topc @ X16 @ X17) @ X15)
% 0.35/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.60          | ~ (l1_pre_topc @ X16))),
% 0.35/0.60      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.35/0.60  thf('81', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (l1_pre_topc @ sk_B)
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.35/0.60          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.35/0.60          | ~ (r1_tarski @ X0 @ sk_D)
% 0.35/0.60          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['79', '80'])).
% 0.35/0.60  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('83', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.35/0.60          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.35/0.60          | ~ (r1_tarski @ X0 @ sk_D)
% 0.35/0.60          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.35/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.35/0.60  thf('84', plain,
% 0.35/0.60      ((![X0 : $i]:
% 0.35/0.60          (~ (r1_tarski @ X0 @ sk_D)
% 0.35/0.60           | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.35/0.60           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.35/0.60         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['78', '83'])).
% 0.35/0.60  thf('85', plain,
% 0.35/0.60      ((((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.35/0.60         | ~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)))
% 0.35/0.60         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['77', '84'])).
% 0.35/0.60  thf('86', plain,
% 0.35/0.60      (((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['72', '85'])).
% 0.35/0.60  thf('87', plain,
% 0.35/0.60      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.35/0.60      inference('split', [status(esa)], ['54'])).
% 0.35/0.60  thf('88', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('89', plain,
% 0.35/0.60      (![X7 : $i, X8 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.35/0.60          | ~ (v4_tops_1 @ X7 @ X8)
% 0.35/0.60          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.35/0.60          | ~ (l1_pre_topc @ X8))),
% 0.35/0.60      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.35/0.60  thf('90', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.35/0.60        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.35/0.60        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.35/0.60  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('92', plain,
% 0.35/0.60      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.35/0.60        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.35/0.60      inference('demod', [status(thm)], ['90', '91'])).
% 0.35/0.60  thf('93', plain,
% 0.35/0.60      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['87', '92'])).
% 0.35/0.60  thf('94', plain,
% 0.35/0.60      (![X0 : $i, X2 : $i]:
% 0.35/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.60  thf('95', plain,
% 0.35/0.60      (((~ (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.35/0.60         | ((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D))))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['93', '94'])).
% 0.35/0.60  thf('96', plain,
% 0.35/0.60      ((((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D)))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['86', '95'])).
% 0.35/0.60  thf('97', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('98', plain,
% 0.35/0.60      (![X9 : $i, X10 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.60          | ((X9) != (k2_pre_topc @ X10 @ (k1_tops_1 @ X10 @ X9)))
% 0.35/0.60          | (v5_tops_1 @ X9 @ X10)
% 0.35/0.60          | ~ (l1_pre_topc @ X10))),
% 0.35/0.60      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.35/0.60  thf('99', plain,
% 0.35/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.35/0.60        | (v5_tops_1 @ sk_D @ sk_B)
% 0.35/0.60        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.35/0.60      inference('sup-', [status(thm)], ['97', '98'])).
% 0.35/0.60  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('101', plain,
% 0.35/0.60      (((v5_tops_1 @ sk_D @ sk_B)
% 0.35/0.60        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.35/0.60      inference('demod', [status(thm)], ['99', '100'])).
% 0.35/0.60  thf('102', plain,
% 0.35/0.60      (((((sk_D) != (sk_D)) | (v5_tops_1 @ sk_D @ sk_B)))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['96', '101'])).
% 0.35/0.60  thf('103', plain,
% 0.35/0.60      (((v5_tops_1 @ sk_D @ sk_B))
% 0.35/0.60         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.35/0.60      inference('simplify', [status(thm)], ['102'])).
% 0.35/0.60  thf('104', plain,
% 0.35/0.60      ((~ (v5_tops_1 @ sk_D @ sk_B)) <= (~ ((v5_tops_1 @ sk_D @ sk_B)))),
% 0.35/0.60      inference('split', [status(esa)], ['46'])).
% 0.35/0.60  thf('105', plain,
% 0.35/0.60      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_D @ sk_B)) | 
% 0.35/0.60       ((v5_tops_1 @ sk_D @ sk_B))),
% 0.35/0.60      inference('sup-', [status(thm)], ['103', '104'])).
% 0.35/0.60  thf('106', plain, ($false),
% 0.35/0.60      inference('sat_resolution*', [status(thm)],
% 0.35/0.60                ['1', '3', '48', '51', '52', '53', '55', '57', '105'])).
% 0.35/0.60  
% 0.35/0.60  % SZS output end Refutation
% 0.35/0.60  
% 0.35/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
