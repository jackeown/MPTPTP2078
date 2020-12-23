%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O8TOg7OkaF

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 276 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          : 1068 (4904 expanded)
%              Number of equality atoms :   29 (  54 expanded)
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

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
      = ( k2_pre_topc @ sk_A @ sk_C ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_pre_topc @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
       != X5 )
      | ( v4_pre_topc @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
     != sk_C )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
     != sk_C ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( sk_C != sk_C )
      | ( v4_pre_topc @ sk_C @ sk_A ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
   <= ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('52',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('54',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('55',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ( r1_tarski @ ( k2_pre_topc @ X14 @ X15 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_D )
        | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['55'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
        = sk_D ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
      = sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9
       != ( k2_pre_topc @ X10 @ ( k1_tops_1 @ X10 @ X9 ) ) )
      | ( v5_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( sk_D != sk_D )
      | ( v5_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
   <= ~ ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('96',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','41','52','53','54','56','58','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O8TOg7OkaF
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:38:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 133 iterations in 0.050s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(t106_tops_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                   ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.21/0.49                       ( v5_tops_1 @ D @ B ) ) & 
% 0.21/0.49                     ( ( v5_tops_1 @ C @ A ) =>
% 0.21/0.49                       ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( l1_pre_topc @ B ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                      ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.21/0.49                          ( v5_tops_1 @ D @ B ) ) & 
% 0.21/0.49                        ( ( v5_tops_1 @ C @ A ) =>
% 0.21/0.49                          ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t106_tops_1])).
% 0.21/0.49  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain, (((v4_pre_topc @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((v4_pre_topc @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain, ((~ (v5_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((v5_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d7_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v5_tops_1 @ B @ A ) <=>
% 0.21/0.50             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.50          | ~ (v5_tops_1 @ X9 @ X10)
% 0.21/0.50          | ((X9) = (k2_pre_topc @ X10 @ (k1_tops_1 @ X10 @ X9)))
% 0.21/0.50          | ~ (l1_pre_topc @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d6_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v4_tops_1 @ B @ A ) <=>
% 0.21/0.50             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.21/0.50               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | ~ (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.21/0.50          | ~ (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.21/0.50          | (v4_tops_1 @ X7 @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v4_tops_1 @ sk_C @ sk_A)
% 0.21/0.50        | ~ (r1_tarski @ sk_C @ 
% 0.21/0.50             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.21/0.50             sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((v4_tops_1 @ sk_C @ sk_A)
% 0.21/0.50        | ~ (r1_tarski @ sk_C @ 
% 0.21/0.50             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.21/0.50             sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((~ (r1_tarski @ sk_C @ sk_C)
% 0.21/0.50         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.21/0.50              sk_C)
% 0.21/0.50         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k1_tops_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf(projectivity_k2_pre_topc, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.21/0.50         ( k2_pre_topc @ A @ B ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X3)
% 0.21/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.50          | ((k2_pre_topc @ X3 @ (k2_pre_topc @ X3 @ X4))
% 0.21/0.50              = (k2_pre_topc @ X3 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.50         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((((k2_pre_topc @ sk_A @ sk_C)
% 0.21/0.50          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['20', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((((sk_C) = (k2_pre_topc @ sk_A @ sk_C)))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t44_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.50          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.50          | ~ (l1_pre_topc @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '19', '32', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((~ (v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.50        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.50        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((((sk_C) = (k2_pre_topc @ sk_A @ sk_C)))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t52_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.50          | ~ (v2_pre_topc @ X6)
% 0.21/0.50          | ((k2_pre_topc @ X6 @ X5) != (X5))
% 0.21/0.50          | (v4_pre_topc @ X5 @ X6)
% 0.21/0.50          | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.50        | ((k2_pre_topc @ sk_A @ sk_C) != (sk_C))
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_C @ sk_A) | ((k2_pre_topc @ sk_A @ sk_C) != (sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((((sk_C) != (sk_C)) | (v4_pre_topc @ sk_C @ sk_A)))
% 0.21/0.50         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((~ (v4_pre_topc @ sk_C @ sk_A)) <= (~ ((v4_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['39'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.50       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['39'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (((v4_tops_1 @ sk_D @ sk_B)
% 0.21/0.50        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.50        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.50       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['55'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_D @ sk_B)
% 0.21/0.50        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.50        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.50       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (((v4_pre_topc @ sk_D @ sk_B)) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['57'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t31_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.50                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.50          | ~ (v4_pre_topc @ X13 @ X14)
% 0.21/0.50          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.50          | (r1_tarski @ (k2_pre_topc @ X14 @ X15) @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.50          | ~ (l1_pre_topc @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.50          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_D)
% 0.21/0.50          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.50          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_D)
% 0.21/0.50          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (r1_tarski @ X0 @ sk_D)
% 0.21/0.50           | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.21/0.50         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '69'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      ((((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.21/0.50         | ~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)))
% 0.21/0.50         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['63', '70'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.50          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.50          | ~ (l1_pre_topc @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_B) | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('76', plain, ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D))
% 0.21/0.50         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['71', '76'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['55'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | ~ (v4_tops_1 @ X7 @ X8)
% 0.21/0.50          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.21/0.50          | ~ (l1_pre_topc @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.50        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.21/0.50        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.50  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.21/0.50        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.21/0.50         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['78', '83'])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (((~ (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.21/0.50         | ((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D))))
% 0.21/0.50         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      ((((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D)))
% 0.21/0.50         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['77', '86'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.50          | ((X9) != (k2_pre_topc @ X10 @ (k1_tops_1 @ X10 @ X9)))
% 0.21/0.50          | (v5_tops_1 @ X9 @ X10)
% 0.21/0.50          | ~ (l1_pre_topc @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.50        | (v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.50        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('91', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      (((v5_tops_1 @ sk_D @ sk_B)
% 0.21/0.50        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.21/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      (((((sk_D) != (sk_D)) | (v5_tops_1 @ sk_D @ sk_B)))
% 0.21/0.50         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['87', '92'])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      (((v5_tops_1 @ sk_D @ sk_B))
% 0.21/0.50         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['93'])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      ((~ (v5_tops_1 @ sk_D @ sk_B)) <= (~ ((v5_tops_1 @ sk_D @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['39'])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_D @ sk_B)) | 
% 0.21/0.50       ((v5_tops_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('97', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['1', '3', '41', '52', '53', '54', '56', '58', '96'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
