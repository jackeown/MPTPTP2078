%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.84euhf8Ahg

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 248 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          : 1047 (4367 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v5_tops_1 @ X7 @ X8 )
      | ( X7
        = ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X6 @ ( k2_pre_topc @ X6 @ X5 ) ) @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ( v4_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
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

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( ( k2_pre_topc @ X3 @ ( k2_pre_topc @ X3 @ X4 ) )
        = ( k2_pre_topc @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('27',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('32',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ sk_C ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','19','32','37'])).

thf('39',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('45',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
   <= ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

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
    inference(split,[status(esa)],['39'])).

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

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ( r1_tarski @ ( k2_pre_topc @ X14 @ X15 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_D )
        | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_tops_1 @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
        = sk_D ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
      = sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7
       != ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ( v5_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( sk_D != sk_D )
      | ( v5_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
   <= ~ ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('95',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','41','51','52','53','55','57','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.84euhf8Ahg
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 135 iterations in 0.057s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.52  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
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
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.52          | ~ (v5_tops_1 @ X7 @ X8)
% 0.21/0.52          | ((X7) = (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.21/0.52          | ~ (l1_pre_topc @ X8))),
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
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.52          | ~ (r1_tarski @ (k1_tops_1 @ X6 @ (k2_pre_topc @ X6 @ X5)) @ X5)
% 0.21/0.52          | ~ (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.21/0.52          | (v4_tops_1 @ X5 @ X6)
% 0.21/0.52          | ~ (l1_pre_topc @ X6))),
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
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k1_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | (m1_subset_1 @ (k1_tops_1 @ X9 @ X10) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(projectivity_k2_pre_topc, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.21/0.52         ( k2_pre_topc @ A @ B ) ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X3)
% 0.21/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.52          | ((k2_pre_topc @ X3 @ (k2_pre_topc @ X3 @ X4))
% 0.21/0.52              = (k2_pre_topc @ X3 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.52         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_C)
% 0.21/0.52          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['20', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ sk_C)))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t44_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.52          | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '19', '32', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((~ (v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.52        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.52         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(fc1_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11)
% 0.21/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.52          | (v4_pre_topc @ (k2_pre_topc @ X11 @ X12) @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['42', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((~ (v4_pre_topc @ sk_C @ sk_A)) <= (~ ((v4_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['39'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['4'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.52       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['39'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.52        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.52       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.52        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.52       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X9)
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | (m1_subset_1 @ (k1_tops_1 @ X9 @ X10) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_D @ sk_B)) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['56'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t31_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.52                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | ~ (v4_pre_topc @ X13 @ X14)
% 0.21/0.52          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ X14 @ X15) @ X13)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | ~ (l1_pre_topc @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_D)
% 0.21/0.52          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.52  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_D)
% 0.21/0.52          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (r1_tarski @ X0 @ sk_D)
% 0.21/0.52           | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.21/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.21/0.52         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['63', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.21/0.52         | ~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)))
% 0.21/0.52         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.52          | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B) | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.52  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('75', plain, ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D))
% 0.21/0.52         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['70', '75'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['54'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.52          | ~ (v4_tops_1 @ X5 @ X6)
% 0.21/0.52          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.21/0.52          | ~ (l1_pre_topc @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.21/0.52        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.21/0.52        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['77', '82'])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      (((~ (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.21/0.52         | ((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D))))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D)))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['76', '85'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.52          | ((X7) != (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.21/0.52          | (v5_tops_1 @ X7 @ X8)
% 0.21/0.52          | ~ (l1_pre_topc @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | (v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (((v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.52        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.21/0.52      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (((((sk_D) != (sk_D)) | (v5_tops_1 @ sk_D @ sk_B)))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['86', '91'])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (((v5_tops_1 @ sk_D @ sk_B))
% 0.21/0.52         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      ((~ (v5_tops_1 @ sk_D @ sk_B)) <= (~ ((v5_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['39'])).
% 0.21/0.52  thf('95', plain,
% 0.21/0.52      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_D @ sk_B)) | 
% 0.21/0.52       ((v5_tops_1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.52  thf('96', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)],
% 0.21/0.52                ['1', '3', '41', '51', '52', '53', '55', '57', '95'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
