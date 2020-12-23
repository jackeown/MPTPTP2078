%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R5Sr4bjpXO

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:55 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 538 expanded)
%              Number of leaves         :   36 ( 167 expanded)
%              Depth                    :   16
%              Number of atoms          : 1900 (8670 expanded)
%              Number of equality atoms :   59 ( 134 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t107_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( v3_pre_topc @ D @ B )
                        & ( v4_tops_1 @ D @ B ) )
                     => ( v6_tops_1 @ D @ B ) )
                    & ( ( v6_tops_1 @ C @ A )
                     => ( ( v3_pre_topc @ C @ A )
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
                   => ( ( ( ( v3_pre_topc @ D @ B )
                          & ( v4_tops_1 @ D @ B ) )
                       => ( v6_tops_1 @ D @ B ) )
                      & ( ( v6_tops_1 @ C @ A )
                       => ( ( v3_pre_topc @ C @ A )
                          & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_tops_1])).

thf('0',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v6_tops_1 @ X22 @ X23 )
      | ( X22
        = ( k1_tops_1 @ X23 @ ( k2_pre_topc @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X28 @ ( k1_tops_1 @ X28 @ X29 ) )
        = ( k1_tops_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('18',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('23',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X21 @ ( k2_pre_topc @ X21 @ X20 ) ) @ X20 )
      | ~ ( r1_tarski @ X20 @ ( k2_pre_topc @ X21 @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ( v4_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','34','35','37'])).

thf('39',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('45',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('54',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['61','64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('72',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['58','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

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

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_B @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('93',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k1_tops_1 @ sk_B @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['85','99'])).

thf('101',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['61','64','69'])).

thf('102',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ ( k1_tops_1 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X14 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['113','118'])).

thf('120',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['102','119'])).

thf('121',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_tops_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ ( k2_pre_topc @ X21 @ X20 ) ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('129',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','129'])).

thf('131',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('133',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( X22
       != ( k1_tops_1 @ X23 @ ( k2_pre_topc @ X23 @ X22 ) ) )
      | ( v6_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(t58_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
            = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('149',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ ( k1_tops_1 @ X36 @ X35 ) )
        = ( k2_pre_topc @ X36 @ ( k1_tops_1 @ X36 @ ( k2_pre_topc @ X36 @ ( k1_tops_1 @ X36 @ X35 ) ) ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t58_tops_1])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
      = ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X28 @ ( k1_tops_1 @ X28 @ X29 ) )
        = ( k1_tops_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('154',plain,
    ( ( ( k1_tops_1 @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
      = ( k1_tops_1 @ sk_B @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k1_tops_1 @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
    = ( k1_tops_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k1_tops_1 @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
    = ( k1_tops_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('158',plain,
    ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
    = ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['150','151','156','157'])).

thf('159',plain,
    ( ( v6_tops_1 @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','158'])).

thf('160',plain,(
    v6_tops_1 @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) @ sk_B ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( v6_tops_1 @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['131','160'])).

thf('162',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['130','161'])).

thf('163',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('164',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','41','51','52','53','55','57','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R5Sr4bjpXO
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:26:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.76/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/1.03  % Solved by: fo/fo7.sh
% 0.76/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.03  % done 1464 iterations in 0.575s
% 0.76/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/1.03  % SZS output start Refutation
% 0.76/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.03  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.76/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.76/1.03  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.76/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/1.03  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.76/1.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/1.03  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.76/1.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/1.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.76/1.03  thf(t107_tops_1, conjecture,
% 0.76/1.03    (![A:$i]:
% 0.76/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/1.03       ( ![B:$i]:
% 0.76/1.03         ( ( l1_pre_topc @ B ) =>
% 0.76/1.03           ( ![C:$i]:
% 0.76/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/1.03               ( ![D:$i]:
% 0.76/1.03                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.76/1.03                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.76/1.03                       ( v6_tops_1 @ D @ B ) ) & 
% 0.76/1.03                     ( ( v6_tops_1 @ C @ A ) =>
% 0.76/1.03                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.03    (~( ![A:$i]:
% 0.76/1.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/1.03          ( ![B:$i]:
% 0.76/1.03            ( ( l1_pre_topc @ B ) =>
% 0.76/1.03              ( ![C:$i]:
% 0.76/1.03                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/1.03                  ( ![D:$i]:
% 0.76/1.03                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.76/1.03                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.76/1.03                          ( v6_tops_1 @ D @ B ) ) & 
% 0.76/1.03                        ( ( v6_tops_1 @ C @ A ) =>
% 0.76/1.03                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/1.03    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.76/1.03  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('split', [status(esa)], ['0'])).
% 0.76/1.03  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('3', plain,
% 0.76/1.03      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('split', [status(esa)], ['2'])).
% 0.76/1.03  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('5', plain,
% 0.76/1.03      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('split', [status(esa)], ['4'])).
% 0.76/1.03  thf('6', plain,
% 0.76/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf(d8_tops_1, axiom,
% 0.76/1.03    (![A:$i]:
% 0.76/1.03     ( ( l1_pre_topc @ A ) =>
% 0.76/1.03       ( ![B:$i]:
% 0.76/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/1.03           ( ( v6_tops_1 @ B @ A ) <=>
% 0.76/1.03             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.76/1.03  thf('7', plain,
% 0.76/1.03      (![X22 : $i, X23 : $i]:
% 0.76/1.03         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.76/1.03          | ~ (v6_tops_1 @ X22 @ X23)
% 0.76/1.03          | ((X22) = (k1_tops_1 @ X23 @ (k2_pre_topc @ X23 @ X22)))
% 0.76/1.03          | ~ (l1_pre_topc @ X23))),
% 0.76/1.03      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.76/1.03  thf('8', plain,
% 0.76/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.76/1.03        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.76/1.03        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/1.03  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('10', plain,
% 0.76/1.03      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.76/1.03        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('demod', [status(thm)], ['8', '9'])).
% 0.76/1.03  thf('11', plain,
% 0.76/1.03      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.76/1.03         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup-', [status(thm)], ['5', '10'])).
% 0.76/1.03  thf('12', plain,
% 0.76/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf(dt_k2_pre_topc, axiom,
% 0.76/1.03    (![A:$i,B:$i]:
% 0.76/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.76/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/1.03       ( m1_subset_1 @
% 0.76/1.03         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/1.03  thf('13', plain,
% 0.76/1.03      (![X12 : $i, X13 : $i]:
% 0.76/1.03         (~ (l1_pre_topc @ X12)
% 0.76/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.76/1.03          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.76/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.76/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.76/1.03  thf('14', plain,
% 0.76/1.03      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.76/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.76/1.03      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/1.03  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('16', plain,
% 0.76/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.76/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/1.03      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/1.03  thf(projectivity_k1_tops_1, axiom,
% 0.76/1.03    (![A:$i,B:$i]:
% 0.76/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.76/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/1.03       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.76/1.03  thf('17', plain,
% 0.76/1.03      (![X28 : $i, X29 : $i]:
% 0.76/1.03         (~ (l1_pre_topc @ X28)
% 0.76/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.76/1.03          | ((k1_tops_1 @ X28 @ (k1_tops_1 @ X28 @ X29))
% 0.76/1.03              = (k1_tops_1 @ X28 @ X29)))),
% 0.76/1.03      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.76/1.03  thf('18', plain,
% 0.76/1.03      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.76/1.03          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.76/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.76/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/1.03  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('20', plain,
% 0.76/1.03      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.76/1.03         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.76/1.03      inference('demod', [status(thm)], ['18', '19'])).
% 0.76/1.03  thf('21', plain,
% 0.76/1.03      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.76/1.03          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.76/1.03         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup+', [status(thm)], ['11', '20'])).
% 0.76/1.03  thf('22', plain,
% 0.76/1.03      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.76/1.03         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup-', [status(thm)], ['5', '10'])).
% 0.76/1.03  thf('23', plain,
% 0.76/1.03      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup+', [status(thm)], ['21', '22'])).
% 0.76/1.03  thf('24', plain,
% 0.76/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf(d6_tops_1, axiom,
% 0.76/1.03    (![A:$i]:
% 0.76/1.03     ( ( l1_pre_topc @ A ) =>
% 0.76/1.03       ( ![B:$i]:
% 0.76/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/1.03           ( ( v4_tops_1 @ B @ A ) <=>
% 0.76/1.03             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.76/1.03               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.76/1.03  thf('25', plain,
% 0.76/1.03      (![X20 : $i, X21 : $i]:
% 0.76/1.03         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.76/1.03          | ~ (r1_tarski @ (k1_tops_1 @ X21 @ (k2_pre_topc @ X21 @ X20)) @ X20)
% 0.76/1.03          | ~ (r1_tarski @ X20 @ (k2_pre_topc @ X21 @ (k1_tops_1 @ X21 @ X20)))
% 0.76/1.03          | (v4_tops_1 @ X20 @ X21)
% 0.76/1.03          | ~ (l1_pre_topc @ X21))),
% 0.76/1.03      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.76/1.03  thf('26', plain,
% 0.76/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.76/1.03        | (v4_tops_1 @ sk_C @ sk_A)
% 0.76/1.03        | ~ (r1_tarski @ sk_C @ 
% 0.76/1.03             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.76/1.03        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.76/1.03             sk_C))),
% 0.76/1.03      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/1.03  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('28', plain,
% 0.76/1.03      (((v4_tops_1 @ sk_C @ sk_A)
% 0.76/1.03        | ~ (r1_tarski @ sk_C @ 
% 0.76/1.03             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.76/1.03        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.76/1.03             sk_C))),
% 0.76/1.03      inference('demod', [status(thm)], ['26', '27'])).
% 0.76/1.03  thf('29', plain,
% 0.76/1.03      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.76/1.03         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.76/1.03              sk_C)
% 0.76/1.03         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup-', [status(thm)], ['23', '28'])).
% 0.76/1.03  thf('30', plain,
% 0.76/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf(t48_pre_topc, axiom,
% 0.76/1.03    (![A:$i]:
% 0.76/1.03     ( ( l1_pre_topc @ A ) =>
% 0.76/1.03       ( ![B:$i]:
% 0.76/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/1.03           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.76/1.03  thf('31', plain,
% 0.76/1.03      (![X14 : $i, X15 : $i]:
% 0.76/1.03         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.76/1.03          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 0.76/1.03          | ~ (l1_pre_topc @ X15))),
% 0.76/1.03      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.76/1.03  thf('32', plain,
% 0.76/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.76/1.03        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.76/1.03      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/1.03  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('34', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.76/1.03      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/1.03  thf('35', plain,
% 0.76/1.03      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.76/1.03         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup-', [status(thm)], ['5', '10'])).
% 0.76/1.03  thf(d10_xboole_0, axiom,
% 0.76/1.03    (![A:$i,B:$i]:
% 0.76/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/1.03  thf('36', plain,
% 0.76/1.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/1.03  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/1.03      inference('simplify', [status(thm)], ['36'])).
% 0.76/1.03  thf('38', plain,
% 0.76/1.03      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('demod', [status(thm)], ['29', '34', '35', '37'])).
% 0.76/1.03  thf('39', plain,
% 0.76/1.03      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.76/1.03        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.76/1.03        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('40', plain,
% 0.76/1.03      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('split', [status(esa)], ['39'])).
% 0.76/1.03  thf('41', plain,
% 0.76/1.03      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('sup-', [status(thm)], ['38', '40'])).
% 0.76/1.03  thf('42', plain,
% 0.76/1.03      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.76/1.03         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup-', [status(thm)], ['5', '10'])).
% 0.76/1.03  thf('43', plain,
% 0.76/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.76/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/1.03      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/1.03  thf(fc9_tops_1, axiom,
% 0.76/1.03    (![A:$i,B:$i]:
% 0.76/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.76/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/1.03       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.76/1.03  thf('44', plain,
% 0.76/1.03      (![X26 : $i, X27 : $i]:
% 0.76/1.03         (~ (l1_pre_topc @ X26)
% 0.76/1.03          | ~ (v2_pre_topc @ X26)
% 0.76/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.76/1.03          | (v3_pre_topc @ (k1_tops_1 @ X26 @ X27) @ X26))),
% 0.76/1.03      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.76/1.03  thf('45', plain,
% 0.76/1.03      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.76/1.03        | ~ (v2_pre_topc @ sk_A)
% 0.76/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.76/1.03      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/1.03  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('48', plain,
% 0.76/1.03      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.76/1.03      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.76/1.03  thf('49', plain,
% 0.76/1.03      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.76/1.03      inference('sup+', [status(thm)], ['42', '48'])).
% 0.76/1.03  thf('50', plain,
% 0.76/1.03      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.76/1.03      inference('split', [status(esa)], ['39'])).
% 0.76/1.03  thf('51', plain,
% 0.76/1.03      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('sup-', [status(thm)], ['49', '50'])).
% 0.76/1.03  thf('52', plain,
% 0.76/1.03      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('split', [status(esa)], ['4'])).
% 0.76/1.03  thf('53', plain,
% 0.76/1.03      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.76/1.03       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('split', [status(esa)], ['39'])).
% 0.76/1.03  thf('54', plain,
% 0.76/1.03      (((v4_tops_1 @ sk_D @ sk_B)
% 0.76/1.03        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.76/1.03        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('55', plain,
% 0.76/1.03      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.76/1.03       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('split', [status(esa)], ['54'])).
% 0.76/1.03  thf('56', plain,
% 0.76/1.03      (((v3_pre_topc @ sk_D @ sk_B)
% 0.76/1.03        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.76/1.03        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.03  thf('57', plain,
% 0.76/1.03      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.76/1.03       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.76/1.03      inference('split', [status(esa)], ['56'])).
% 0.76/1.03  thf('58', plain,
% 0.76/1.03      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.76/1.03      inference('split', [status(esa)], ['56'])).
% 0.85/1.03  thf('59', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(involutiveness_k3_subset_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.03       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.85/1.03  thf('60', plain,
% 0.85/1.03      (![X7 : $i, X8 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.85/1.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.85/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.85/1.03  thf('61', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.85/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.85/1.03  thf('62', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(d5_subset_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.03       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf('63', plain,
% 0.85/1.03      (![X5 : $i, X6 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.85/1.03          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('64', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.85/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.85/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.85/1.03  thf(t36_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.85/1.03  thf('65', plain,
% 0.85/1.03      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.85/1.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.03  thf(t3_subset, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.85/1.03  thf('66', plain,
% 0.85/1.03      (![X9 : $i, X11 : $i]:
% 0.85/1.03         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.85/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.85/1.03  thf('67', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.03  thf('68', plain,
% 0.85/1.03      (![X5 : $i, X6 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.85/1.03          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('69', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.85/1.03           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['67', '68'])).
% 0.85/1.03  thf('70', plain,
% 0.85/1.03      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03         (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.85/1.03      inference('demod', [status(thm)], ['61', '64', '69'])).
% 0.85/1.03  thf('71', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.03  thf(t29_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( v4_pre_topc @ B @ A ) <=>
% 0.85/1.03             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.85/1.03  thf('72', plain,
% 0.85/1.03      (![X30 : $i, X31 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.85/1.03          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.85/1.03          | (v4_pre_topc @ X30 @ X31)
% 0.85/1.03          | ~ (l1_pre_topc @ X31))),
% 0.85/1.03      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.85/1.03  thf('73', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X0)
% 0.85/1.03          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.85/1.03          | ~ (v3_pre_topc @ 
% 0.85/1.03               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.85/1.03                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.85/1.03               X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['71', '72'])).
% 0.85/1.03  thf('74', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.85/1.03           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['67', '68'])).
% 0.85/1.03  thf('75', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X0)
% 0.85/1.03          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.85/1.03          | ~ (v3_pre_topc @ 
% 0.85/1.03               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.85/1.03                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.85/1.03               X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.85/1.03  thf('76', plain,
% 0.85/1.03      ((~ (v3_pre_topc @ sk_D @ sk_B)
% 0.85/1.03        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['70', '75'])).
% 0.85/1.03  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('78', plain,
% 0.85/1.03      ((~ (v3_pre_topc @ sk_D @ sk_B)
% 0.85/1.03        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['76', '77'])).
% 0.85/1.03  thf('79', plain,
% 0.85/1.03      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['58', '78'])).
% 0.85/1.03  thf('80', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.03  thf(t52_pre_topc, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.85/1.03             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.85/1.03               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.85/1.03  thf('81', plain,
% 0.85/1.03      (![X16 : $i, X17 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.85/1.03          | ~ (v4_pre_topc @ X16 @ X17)
% 0.85/1.03          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.85/1.03          | ~ (l1_pre_topc @ X17))),
% 0.85/1.03      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.85/1.03  thf('82', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X0)
% 0.85/1.03          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.85/1.03              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.85/1.03          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.85/1.03  thf('83', plain,
% 0.85/1.03      (((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.85/1.03           = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.85/1.03         | ~ (l1_pre_topc @ sk_B))) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['79', '82'])).
% 0.85/1.03  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('85', plain,
% 0.85/1.03      ((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['83', '84'])).
% 0.85/1.03  thf('86', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(d1_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( k1_tops_1 @ A @ B ) =
% 0.85/1.03             ( k3_subset_1 @
% 0.85/1.03               ( u1_struct_0 @ A ) @ 
% 0.85/1.03               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.85/1.03  thf('87', plain,
% 0.85/1.03      (![X18 : $i, X19 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.85/1.03          | ((k1_tops_1 @ X19 @ X18)
% 0.85/1.03              = (k3_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.85/1.03                 (k2_pre_topc @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18))))
% 0.85/1.03          | ~ (l1_pre_topc @ X19))),
% 0.85/1.03      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.85/1.03  thf('88', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.03        | ((k1_tops_1 @ sk_B @ sk_D)
% 0.85/1.03            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03               (k2_pre_topc @ sk_B @ 
% 0.85/1.03                (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['86', '87'])).
% 0.85/1.03  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('90', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.85/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.85/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.85/1.03  thf('91', plain,
% 0.85/1.03      (((k1_tops_1 @ sk_B @ sk_D)
% 0.85/1.03         = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03            (k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.85/1.03      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.85/1.03  thf('92', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.03  thf('93', plain,
% 0.85/1.03      (![X12 : $i, X13 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X12)
% 0.85/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.85/1.03          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.85/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.85/1.03  thf('94', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((m1_subset_1 @ 
% 0.85/1.03           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.85/1.03           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.85/1.03          | ~ (l1_pre_topc @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['92', '93'])).
% 0.85/1.03  thf('95', plain,
% 0.85/1.03      (![X5 : $i, X6 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.85/1.03          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('96', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X0)
% 0.85/1.03          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.85/1.03              (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))
% 0.85/1.03              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.85/1.03                 (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['94', '95'])).
% 0.85/1.03  thf('97', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03             (k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup+', [status(thm)], ['91', '96'])).
% 0.85/1.03  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('99', plain,
% 0.85/1.03      (((k1_tops_1 @ sk_B @ sk_D)
% 0.85/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03            (k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.85/1.03      inference('demod', [status(thm)], ['97', '98'])).
% 0.85/1.03  thf('100', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03             (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['85', '99'])).
% 0.85/1.03  thf('101', plain,
% 0.85/1.03      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.85/1.03         (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.85/1.03      inference('demod', [status(thm)], ['61', '64', '69'])).
% 0.85/1.03  thf('102', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['100', '101'])).
% 0.85/1.03  thf('103', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('104', plain,
% 0.85/1.03      (![X12 : $i, X13 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X12)
% 0.85/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.85/1.03          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.85/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.85/1.03  thf('105', plain,
% 0.85/1.03      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['103', '104'])).
% 0.85/1.03  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('107', plain,
% 0.85/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['105', '106'])).
% 0.85/1.03  thf('108', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(t48_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ![C:$i]:
% 0.85/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03               ( ( r1_tarski @ B @ C ) =>
% 0.85/1.03                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.85/1.03  thf('109', plain,
% 0.85/1.03      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.85/1.03          | ~ (r1_tarski @ X32 @ X34)
% 0.85/1.03          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ (k1_tops_1 @ X33 @ X34))
% 0.85/1.03          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.85/1.03          | ~ (l1_pre_topc @ X33))),
% 0.85/1.03      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.85/1.03  thf('110', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ sk_B)
% 0.85/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.85/1.03          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.85/1.03          | ~ (r1_tarski @ sk_D @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['108', '109'])).
% 0.85/1.03  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('112', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.85/1.03          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.85/1.03          | ~ (r1_tarski @ sk_D @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['110', '111'])).
% 0.85/1.03  thf('113', plain,
% 0.85/1.03      ((~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))
% 0.85/1.03        | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.85/1.03           (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['107', '112'])).
% 0.85/1.03  thf('114', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('115', plain,
% 0.85/1.03      (![X14 : $i, X15 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.85/1.03          | (r1_tarski @ X14 @ (k2_pre_topc @ X15 @ X14))
% 0.85/1.03          | ~ (l1_pre_topc @ X15))),
% 0.85/1.03      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.85/1.03  thf('116', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.03        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['114', '115'])).
% 0.85/1.03  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('118', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.85/1.03      inference('demod', [status(thm)], ['116', '117'])).
% 0.85/1.03  thf('119', plain,
% 0.85/1.03      ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.85/1.03        (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.85/1.03      inference('demod', [status(thm)], ['113', '118'])).
% 0.85/1.03  thf('120', plain,
% 0.85/1.03      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['102', '119'])).
% 0.85/1.03  thf('121', plain,
% 0.85/1.03      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.85/1.03      inference('split', [status(esa)], ['54'])).
% 0.85/1.03  thf('122', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('123', plain,
% 0.85/1.03      (![X20 : $i, X21 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.85/1.03          | ~ (v4_tops_1 @ X20 @ X21)
% 0.85/1.03          | (r1_tarski @ (k1_tops_1 @ X21 @ (k2_pre_topc @ X21 @ X20)) @ X20)
% 0.85/1.03          | ~ (l1_pre_topc @ X21))),
% 0.85/1.03      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.85/1.03  thf('124', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.03        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.85/1.03        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['122', '123'])).
% 0.85/1.03  thf('125', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('126', plain,
% 0.85/1.03      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.85/1.03        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['124', '125'])).
% 0.85/1.03  thf('127', plain,
% 0.85/1.03      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.85/1.03         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['121', '126'])).
% 0.85/1.03  thf('128', plain,
% 0.85/1.03      (![X0 : $i, X2 : $i]:
% 0.85/1.03         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('129', plain,
% 0.85/1.03      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.85/1.03         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.85/1.03         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['127', '128'])).
% 0.85/1.03  thf('130', plain,
% 0.85/1.03      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.85/1.03         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['120', '129'])).
% 0.85/1.03  thf('131', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['100', '101'])).
% 0.85/1.03  thf('132', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(dt_k1_tops_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.85/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.03       ( m1_subset_1 @
% 0.85/1.03         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.85/1.03  thf('133', plain,
% 0.85/1.03      (![X24 : $i, X25 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X24)
% 0.85/1.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.85/1.03          | (m1_subset_1 @ (k1_tops_1 @ X24 @ X25) @ 
% 0.85/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.85/1.03  thf('134', plain,
% 0.85/1.03      (((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['132', '133'])).
% 0.85/1.03  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('136', plain,
% 0.85/1.03      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['134', '135'])).
% 0.85/1.03  thf('137', plain,
% 0.85/1.03      (![X12 : $i, X13 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X12)
% 0.85/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.85/1.03          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.85/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.85/1.03  thf('138', plain,
% 0.85/1.03      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['136', '137'])).
% 0.85/1.03  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('140', plain,
% 0.85/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['138', '139'])).
% 0.85/1.03  thf('141', plain,
% 0.85/1.03      (![X24 : $i, X25 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X24)
% 0.85/1.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.85/1.03          | (m1_subset_1 @ (k1_tops_1 @ X24 @ X25) @ 
% 0.85/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.85/1.03  thf('142', plain,
% 0.85/1.03      (((m1_subset_1 @ 
% 0.85/1.03         (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['140', '141'])).
% 0.85/1.03  thf('143', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('144', plain,
% 0.85/1.03      ((m1_subset_1 @ 
% 0.85/1.03        (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['142', '143'])).
% 0.85/1.03  thf('145', plain,
% 0.85/1.03      (![X22 : $i, X23 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.85/1.03          | ((X22) != (k1_tops_1 @ X23 @ (k2_pre_topc @ X23 @ X22)))
% 0.85/1.03          | (v6_tops_1 @ X22 @ X23)
% 0.85/1.03          | ~ (l1_pre_topc @ X23))),
% 0.85/1.03      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.85/1.03  thf('146', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.03        | (v6_tops_1 @ 
% 0.85/1.03           (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))) @ 
% 0.85/1.03           sk_B)
% 0.85/1.03        | ((k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.85/1.03            != (k1_tops_1 @ sk_B @ 
% 0.85/1.03                (k2_pre_topc @ sk_B @ 
% 0.85/1.03                 (k1_tops_1 @ sk_B @ 
% 0.85/1.03                  (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['144', '145'])).
% 0.85/1.03  thf('147', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('148', plain,
% 0.85/1.03      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['134', '135'])).
% 0.85/1.03  thf(t58_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.85/1.03             ( k2_pre_topc @
% 0.85/1.03               A @ 
% 0.85/1.03               ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.85/1.03  thf('149', plain,
% 0.85/1.03      (![X35 : $i, X36 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.85/1.03          | ((k2_pre_topc @ X36 @ (k1_tops_1 @ X36 @ X35))
% 0.85/1.03              = (k2_pre_topc @ X36 @ 
% 0.85/1.03                 (k1_tops_1 @ X36 @ 
% 0.85/1.03                  (k2_pre_topc @ X36 @ (k1_tops_1 @ X36 @ X35)))))
% 0.85/1.03          | ~ (l1_pre_topc @ X36))),
% 0.85/1.03      inference('cnf', [status(esa)], [t58_tops_1])).
% 0.85/1.03  thf('150', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.03        | ((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.85/1.03            = (k2_pre_topc @ sk_B @ 
% 0.85/1.03               (k1_tops_1 @ sk_B @ 
% 0.85/1.03                (k2_pre_topc @ sk_B @ 
% 0.85/1.03                 (k1_tops_1 @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['148', '149'])).
% 0.85/1.03  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('152', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('153', plain,
% 0.85/1.03      (![X28 : $i, X29 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X28)
% 0.85/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.85/1.03          | ((k1_tops_1 @ X28 @ (k1_tops_1 @ X28 @ X29))
% 0.85/1.03              = (k1_tops_1 @ X28 @ X29)))),
% 0.85/1.03      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.85/1.03  thf('154', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))
% 0.85/1.03          = (k1_tops_1 @ sk_B @ sk_D))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['152', '153'])).
% 0.85/1.03  thf('155', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('156', plain,
% 0.85/1.03      (((k1_tops_1 @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))
% 0.85/1.03         = (k1_tops_1 @ sk_B @ sk_D))),
% 0.85/1.03      inference('demod', [status(thm)], ['154', '155'])).
% 0.85/1.03  thf('157', plain,
% 0.85/1.03      (((k1_tops_1 @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))
% 0.85/1.03         = (k1_tops_1 @ sk_B @ sk_D))),
% 0.85/1.03      inference('demod', [status(thm)], ['154', '155'])).
% 0.85/1.03  thf('158', plain,
% 0.85/1.03      (((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))
% 0.85/1.03         = (k2_pre_topc @ sk_B @ 
% 0.85/1.03            (k1_tops_1 @ sk_B @ 
% 0.85/1.03             (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))))),
% 0.85/1.03      inference('demod', [status(thm)], ['150', '151', '156', '157'])).
% 0.85/1.03  thf('159', plain,
% 0.85/1.03      (((v6_tops_1 @ 
% 0.85/1.03         (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))) @ 
% 0.85/1.03         sk_B)
% 0.85/1.03        | ((k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.85/1.03            != (k1_tops_1 @ sk_B @ 
% 0.85/1.03                (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))))),
% 0.85/1.03      inference('demod', [status(thm)], ['146', '147', '158'])).
% 0.85/1.03  thf('160', plain,
% 0.85/1.03      ((v6_tops_1 @ 
% 0.85/1.03        (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))) @ 
% 0.85/1.03        sk_B)),
% 0.85/1.03      inference('simplify', [status(thm)], ['159'])).
% 0.85/1.03  thf('161', plain,
% 0.85/1.03      (((v6_tops_1 @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_B))
% 0.85/1.03         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['131', '160'])).
% 0.85/1.03  thf('162', plain,
% 0.85/1.03      (((v6_tops_1 @ sk_D @ sk_B))
% 0.85/1.03         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['130', '161'])).
% 0.85/1.03  thf('163', plain,
% 0.85/1.03      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.85/1.03      inference('split', [status(esa)], ['39'])).
% 0.85/1.03  thf('164', plain,
% 0.85/1.03      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.85/1.03       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['162', '163'])).
% 0.85/1.03  thf('165', plain, ($false),
% 0.85/1.03      inference('sat_resolution*', [status(thm)],
% 0.85/1.03                ['1', '3', '41', '51', '52', '53', '55', '57', '164'])).
% 0.85/1.03  
% 0.85/1.03  % SZS output end Refutation
% 0.85/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
