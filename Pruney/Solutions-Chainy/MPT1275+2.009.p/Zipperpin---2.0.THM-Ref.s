%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUCkzyttSP

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:33 EST 2020

% Result     : Theorem 3.29s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 252 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  855 (2968 expanded)
%              Number of equality atoms :   31 ( 149 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( r1_tarski @ X25 @ ( k2_tops_1 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tops_1 @ X27 @ X28 )
      | ~ ( v3_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ ( k2_tops_1 @ X26 @ X25 ) )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X24 @ X23 ) @ X24 )
      | ( v3_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','33'])).

thf('35',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['13','37','38'])).

thf('40',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['11','39'])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('45',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['13','37'])).

thf('46',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('51',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X15 @ X16 ) @ ( k3_subset_1 @ X15 @ ( k9_subset_1 @ X15 @ X16 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('64',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','64'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X12 @ X11 ) @ ( k3_subset_1 @ X12 @ X13 ) )
      | ( r1_tarski @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('70',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['67','72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['47','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUCkzyttSP
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:12:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.29/3.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.29/3.46  % Solved by: fo/fo7.sh
% 3.29/3.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.29/3.46  % done 2122 iterations in 3.003s
% 3.29/3.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.29/3.46  % SZS output start Refutation
% 3.29/3.46  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.29/3.46  thf(sk_B_type, type, sk_B: $i).
% 3.29/3.46  thf(sk_A_type, type, sk_A: $i).
% 3.29/3.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.29/3.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.29/3.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.29/3.46  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 3.29/3.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.29/3.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.29/3.46  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 3.29/3.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.29/3.46  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.29/3.46  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.29/3.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.29/3.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.29/3.46  thf(t94_tops_1, conjecture,
% 3.29/3.46    (![A:$i]:
% 3.29/3.46     ( ( l1_pre_topc @ A ) =>
% 3.29/3.46       ( ![B:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46           ( ( v4_pre_topc @ B @ A ) =>
% 3.29/3.46             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 3.29/3.46  thf(zf_stmt_0, negated_conjecture,
% 3.29/3.46    (~( ![A:$i]:
% 3.29/3.46        ( ( l1_pre_topc @ A ) =>
% 3.29/3.46          ( ![B:$i]:
% 3.29/3.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46              ( ( v4_pre_topc @ B @ A ) =>
% 3.29/3.46                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 3.29/3.46    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 3.29/3.46  thf('0', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf(t88_tops_1, axiom,
% 3.29/3.46    (![A:$i]:
% 3.29/3.46     ( ( l1_pre_topc @ A ) =>
% 3.29/3.46       ( ![B:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46           ( ( v2_tops_1 @ B @ A ) <=>
% 3.29/3.46             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.29/3.46  thf('1', plain,
% 3.29/3.46      (![X25 : $i, X26 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.29/3.46          | ~ (v2_tops_1 @ X25 @ X26)
% 3.29/3.46          | (r1_tarski @ X25 @ (k2_tops_1 @ X26 @ X25))
% 3.29/3.46          | ~ (l1_pre_topc @ X26))),
% 3.29/3.46      inference('cnf', [status(esa)], [t88_tops_1])).
% 3.29/3.46  thf('2', plain,
% 3.29/3.46      ((~ (l1_pre_topc @ sk_A)
% 3.29/3.46        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.29/3.46        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('sup-', [status(thm)], ['0', '1'])).
% 3.29/3.46  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('4', plain,
% 3.29/3.46      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('5', plain,
% 3.29/3.46      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 3.29/3.46      inference('split', [status(esa)], ['4'])).
% 3.29/3.46  thf('6', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf(t92_tops_1, axiom,
% 3.29/3.46    (![A:$i]:
% 3.29/3.46     ( ( l1_pre_topc @ A ) =>
% 3.29/3.46       ( ![B:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 3.29/3.46  thf('7', plain,
% 3.29/3.46      (![X27 : $i, X28 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 3.29/3.46          | (v2_tops_1 @ X27 @ X28)
% 3.29/3.46          | ~ (v3_tops_1 @ X27 @ X28)
% 3.29/3.46          | ~ (l1_pre_topc @ X28))),
% 3.29/3.46      inference('cnf', [status(esa)], [t92_tops_1])).
% 3.29/3.46  thf('8', plain,
% 3.29/3.46      ((~ (l1_pre_topc @ sk_A)
% 3.29/3.46        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 3.29/3.46        | (v2_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('sup-', [status(thm)], ['6', '7'])).
% 3.29/3.46  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('10', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('demod', [status(thm)], ['8', '9'])).
% 3.29/3.46  thf('11', plain,
% 3.29/3.46      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 3.29/3.46      inference('sup-', [status(thm)], ['5', '10'])).
% 3.29/3.46  thf('12', plain,
% 3.29/3.46      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('13', plain,
% 3.29/3.46      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('split', [status(esa)], ['12'])).
% 3.29/3.46  thf('14', plain,
% 3.29/3.46      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 3.29/3.46         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 3.29/3.46      inference('split', [status(esa)], ['4'])).
% 3.29/3.46  thf('15', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('16', plain,
% 3.29/3.46      (![X25 : $i, X26 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.29/3.46          | ~ (r1_tarski @ X25 @ (k2_tops_1 @ X26 @ X25))
% 3.29/3.46          | (v2_tops_1 @ X25 @ X26)
% 3.29/3.46          | ~ (l1_pre_topc @ X26))),
% 3.29/3.46      inference('cnf', [status(esa)], [t88_tops_1])).
% 3.29/3.46  thf('17', plain,
% 3.29/3.46      ((~ (l1_pre_topc @ sk_A)
% 3.29/3.46        | (v2_tops_1 @ sk_B @ sk_A)
% 3.29/3.46        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.29/3.46      inference('sup-', [status(thm)], ['15', '16'])).
% 3.29/3.46  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('19', plain,
% 3.29/3.46      (((v2_tops_1 @ sk_B @ sk_A)
% 3.29/3.46        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.29/3.46      inference('demod', [status(thm)], ['17', '18'])).
% 3.29/3.46  thf('20', plain,
% 3.29/3.46      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 3.29/3.46         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 3.29/3.46      inference('sup-', [status(thm)], ['14', '19'])).
% 3.29/3.46  thf(d10_xboole_0, axiom,
% 3.29/3.46    (![A:$i,B:$i]:
% 3.29/3.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.29/3.46  thf('21', plain,
% 3.29/3.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.29/3.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.29/3.46  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.29/3.46      inference('simplify', [status(thm)], ['21'])).
% 3.29/3.46  thf('23', plain,
% 3.29/3.46      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 3.29/3.46      inference('demod', [status(thm)], ['20', '22'])).
% 3.29/3.46  thf('24', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf(d5_tops_1, axiom,
% 3.29/3.46    (![A:$i]:
% 3.29/3.46     ( ( l1_pre_topc @ A ) =>
% 3.29/3.46       ( ![B:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46           ( ( v3_tops_1 @ B @ A ) <=>
% 3.29/3.46             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 3.29/3.46  thf('25', plain,
% 3.29/3.46      (![X23 : $i, X24 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.29/3.46          | ~ (v2_tops_1 @ (k2_pre_topc @ X24 @ X23) @ X24)
% 3.29/3.46          | (v3_tops_1 @ X23 @ X24)
% 3.29/3.46          | ~ (l1_pre_topc @ X24))),
% 3.29/3.46      inference('cnf', [status(esa)], [d5_tops_1])).
% 3.29/3.46  thf('26', plain,
% 3.29/3.46      ((~ (l1_pre_topc @ sk_A)
% 3.29/3.46        | (v3_tops_1 @ sk_B @ sk_A)
% 3.29/3.46        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 3.29/3.46      inference('sup-', [status(thm)], ['24', '25'])).
% 3.29/3.46  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('28', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf(t52_pre_topc, axiom,
% 3.29/3.46    (![A:$i]:
% 3.29/3.46     ( ( l1_pre_topc @ A ) =>
% 3.29/3.46       ( ![B:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.29/3.46             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.29/3.46               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.29/3.46  thf('29', plain,
% 3.29/3.46      (![X19 : $i, X20 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 3.29/3.46          | ~ (v4_pre_topc @ X19 @ X20)
% 3.29/3.46          | ((k2_pre_topc @ X20 @ X19) = (X19))
% 3.29/3.46          | ~ (l1_pre_topc @ X20))),
% 3.29/3.46      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.29/3.46  thf('30', plain,
% 3.29/3.46      ((~ (l1_pre_topc @ sk_A)
% 3.29/3.46        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 3.29/3.46        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.29/3.46      inference('sup-', [status(thm)], ['28', '29'])).
% 3.29/3.46  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('32', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 3.29/3.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 3.29/3.46  thf('34', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('demod', [status(thm)], ['26', '27', '33'])).
% 3.29/3.46  thf('35', plain,
% 3.29/3.46      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 3.29/3.46      inference('sup-', [status(thm)], ['23', '34'])).
% 3.29/3.46  thf('36', plain,
% 3.29/3.46      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 3.29/3.46      inference('split', [status(esa)], ['12'])).
% 3.29/3.46  thf('37', plain,
% 3.29/3.46      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 3.29/3.46      inference('sup-', [status(thm)], ['35', '36'])).
% 3.29/3.46  thf('38', plain,
% 3.29/3.46      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 3.29/3.46      inference('split', [status(esa)], ['4'])).
% 3.29/3.46  thf('39', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 3.29/3.46      inference('sat_resolution*', [status(thm)], ['13', '37', '38'])).
% 3.29/3.46  thf('40', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 3.29/3.46      inference('simpl_trail', [status(thm)], ['11', '39'])).
% 3.29/3.46  thf('41', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 3.29/3.46      inference('demod', [status(thm)], ['2', '3', '40'])).
% 3.29/3.46  thf('42', plain,
% 3.29/3.46      (![X0 : $i, X2 : $i]:
% 3.29/3.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.29/3.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.29/3.46  thf('43', plain,
% 3.29/3.46      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.29/3.46        | ((k2_tops_1 @ sk_A @ sk_B) = (sk_B)))),
% 3.29/3.46      inference('sup-', [status(thm)], ['41', '42'])).
% 3.29/3.46  thf('44', plain,
% 3.29/3.46      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.29/3.46         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 3.29/3.46      inference('split', [status(esa)], ['12'])).
% 3.29/3.46  thf('45', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 3.29/3.46      inference('sat_resolution*', [status(thm)], ['13', '37'])).
% 3.29/3.46  thf('46', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 3.29/3.46      inference('simpl_trail', [status(thm)], ['44', '45'])).
% 3.29/3.46  thf('47', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 3.29/3.46      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 3.29/3.46  thf('48', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('49', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf(dt_k3_subset_1, axiom,
% 3.29/3.46    (![A:$i,B:$i]:
% 3.29/3.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.29/3.46       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.29/3.46  thf('50', plain,
% 3.29/3.46      (![X6 : $i, X7 : $i]:
% 3.29/3.46         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 3.29/3.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 3.29/3.46      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.29/3.46  thf('51', plain,
% 3.29/3.46      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.29/3.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('sup-', [status(thm)], ['49', '50'])).
% 3.29/3.46  thf(dt_k2_pre_topc, axiom,
% 3.29/3.46    (![A:$i,B:$i]:
% 3.29/3.46     ( ( ( l1_pre_topc @ A ) & 
% 3.29/3.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.29/3.46       ( m1_subset_1 @
% 3.29/3.46         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.29/3.46  thf('52', plain,
% 3.29/3.46      (![X17 : $i, X18 : $i]:
% 3.29/3.46         (~ (l1_pre_topc @ X17)
% 3.29/3.46          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.29/3.46          | (m1_subset_1 @ (k2_pre_topc @ X17 @ X18) @ 
% 3.29/3.46             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 3.29/3.46      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.29/3.46  thf('53', plain,
% 3.29/3.46      (((m1_subset_1 @ 
% 3.29/3.46         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.29/3.46         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.29/3.46        | ~ (l1_pre_topc @ sk_A))),
% 3.29/3.46      inference('sup-', [status(thm)], ['51', '52'])).
% 3.29/3.46  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('55', plain,
% 3.29/3.46      ((m1_subset_1 @ 
% 3.29/3.46        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.29/3.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('demod', [status(thm)], ['53', '54'])).
% 3.29/3.46  thf(t42_subset_1, axiom,
% 3.29/3.46    (![A:$i,B:$i]:
% 3.29/3.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.29/3.46       ( ![C:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.29/3.46           ( r1_tarski @
% 3.29/3.46             ( k3_subset_1 @ A @ B ) @ 
% 3.29/3.46             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.29/3.46  thf('56', plain,
% 3.29/3.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.29/3.46          | (r1_tarski @ (k3_subset_1 @ X15 @ X16) @ 
% 3.29/3.46             (k3_subset_1 @ X15 @ (k9_subset_1 @ X15 @ X16 @ X14)))
% 3.29/3.46          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 3.29/3.46      inference('cnf', [status(esa)], [t42_subset_1])).
% 3.29/3.46  thf('57', plain,
% 3.29/3.46      (![X0 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.29/3.46          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 3.29/3.46             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.29/3.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 3.29/3.46               (k2_pre_topc @ sk_A @ 
% 3.29/3.46                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 3.29/3.46      inference('sup-', [status(thm)], ['55', '56'])).
% 3.29/3.46  thf('58', plain,
% 3.29/3.46      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.29/3.46        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.29/3.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.29/3.46          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.29/3.46      inference('sup-', [status(thm)], ['48', '57'])).
% 3.29/3.46  thf('59', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf(d2_tops_1, axiom,
% 3.29/3.46    (![A:$i]:
% 3.29/3.46     ( ( l1_pre_topc @ A ) =>
% 3.29/3.46       ( ![B:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.29/3.46           ( ( k2_tops_1 @ A @ B ) =
% 3.29/3.46             ( k9_subset_1 @
% 3.29/3.46               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.29/3.46               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 3.29/3.46  thf('60', plain,
% 3.29/3.46      (![X21 : $i, X22 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.29/3.46          | ((k2_tops_1 @ X22 @ X21)
% 3.29/3.46              = (k9_subset_1 @ (u1_struct_0 @ X22) @ 
% 3.29/3.46                 (k2_pre_topc @ X22 @ X21) @ 
% 3.29/3.46                 (k2_pre_topc @ X22 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21))))
% 3.29/3.46          | ~ (l1_pre_topc @ X22))),
% 3.29/3.46      inference('cnf', [status(esa)], [d2_tops_1])).
% 3.29/3.46  thf('61', plain,
% 3.29/3.46      ((~ (l1_pre_topc @ sk_A)
% 3.29/3.46        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.29/3.46            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.29/3.46               (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.29/3.46               (k2_pre_topc @ sk_A @ 
% 3.29/3.46                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.29/3.46      inference('sup-', [status(thm)], ['59', '60'])).
% 3.29/3.46  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('63', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 3.29/3.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 3.29/3.46  thf('64', plain,
% 3.29/3.46      (((k2_tops_1 @ sk_A @ sk_B)
% 3.29/3.46         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.29/3.46            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.29/3.46      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.29/3.46  thf('65', plain,
% 3.29/3.46      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.29/3.46        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.29/3.46      inference('demod', [status(thm)], ['58', '64'])).
% 3.29/3.46  thf(t31_subset_1, axiom,
% 3.29/3.46    (![A:$i,B:$i]:
% 3.29/3.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.29/3.46       ( ![C:$i]:
% 3.29/3.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.29/3.46           ( ( r1_tarski @ B @ C ) <=>
% 3.29/3.46             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 3.29/3.46  thf('66', plain,
% 3.29/3.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.29/3.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 3.29/3.46          | ~ (r1_tarski @ (k3_subset_1 @ X12 @ X11) @ 
% 3.29/3.46               (k3_subset_1 @ X12 @ X13))
% 3.29/3.46          | (r1_tarski @ X13 @ X11)
% 3.29/3.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 3.29/3.46      inference('cnf', [status(esa)], [t31_subset_1])).
% 3.29/3.46  thf('67', plain,
% 3.29/3.46      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.29/3.46           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.29/3.46        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.29/3.46        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.29/3.46      inference('sup-', [status(thm)], ['65', '66'])).
% 3.29/3.46  thf('68', plain,
% 3.29/3.46      (((k2_tops_1 @ sk_A @ sk_B)
% 3.29/3.46         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.29/3.46            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.29/3.46      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.29/3.46  thf('69', plain,
% 3.29/3.46      ((m1_subset_1 @ 
% 3.29/3.46        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.29/3.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('demod', [status(thm)], ['53', '54'])).
% 3.29/3.46  thf(dt_k9_subset_1, axiom,
% 3.29/3.46    (![A:$i,B:$i,C:$i]:
% 3.29/3.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.29/3.46       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.29/3.46  thf('70', plain,
% 3.29/3.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.29/3.46         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 3.29/3.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 3.29/3.46      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 3.29/3.46  thf('71', plain,
% 3.29/3.46      (![X0 : $i]:
% 3.29/3.46         (m1_subset_1 @ 
% 3.29/3.46          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 3.29/3.46           (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 3.29/3.46          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('sup-', [status(thm)], ['69', '70'])).
% 3.29/3.46  thf('72', plain,
% 3.29/3.46      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.29/3.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('sup+', [status(thm)], ['68', '71'])).
% 3.29/3.46  thf('73', plain,
% 3.29/3.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.29/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.29/3.46  thf('74', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 3.29/3.46      inference('demod', [status(thm)], ['67', '72', '73'])).
% 3.29/3.46  thf('75', plain, ($false), inference('demod', [status(thm)], ['47', '74'])).
% 3.29/3.46  
% 3.29/3.46  % SZS output end Refutation
% 3.29/3.46  
% 3.29/3.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
