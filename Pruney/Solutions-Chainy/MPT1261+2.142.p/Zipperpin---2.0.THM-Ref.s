%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HoFQXmQXXV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:59 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 318 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          : 1278 (4253 expanded)
%              Number of equality atoms :   90 ( 242 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_tops_1 @ X29 @ X28 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k2_pre_topc @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('26',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('27',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('28',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('29',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28','29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X24 @ ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X31 @ X30 ) @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('59',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_tops_1 @ X29 @ X28 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k2_pre_topc @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('84',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('86',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('87',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','92'])).

thf('94',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
       != X26 )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HoFQXmQXXV
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:25:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 2.21/2.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.21/2.40  % Solved by: fo/fo7.sh
% 2.21/2.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.40  % done 3515 iterations in 1.921s
% 2.21/2.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.21/2.40  % SZS output start Refutation
% 2.21/2.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.21/2.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.21/2.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.21/2.40  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.21/2.40  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.21/2.40  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.21/2.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.21/2.40  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.21/2.40  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.21/2.40  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.21/2.40  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.21/2.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.21/2.40  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.40  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.21/2.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.21/2.40  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.21/2.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.21/2.40  thf(t77_tops_1, conjecture,
% 2.21/2.40    (![A:$i]:
% 2.21/2.40     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.21/2.40       ( ![B:$i]:
% 2.21/2.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.21/2.40           ( ( v4_pre_topc @ B @ A ) <=>
% 2.21/2.40             ( ( k2_tops_1 @ A @ B ) =
% 2.21/2.40               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.21/2.40  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.40    (~( ![A:$i]:
% 2.21/2.40        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.21/2.40          ( ![B:$i]:
% 2.21/2.40            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.21/2.40              ( ( v4_pre_topc @ B @ A ) <=>
% 2.21/2.40                ( ( k2_tops_1 @ A @ B ) =
% 2.21/2.40                  ( k7_subset_1 @
% 2.21/2.40                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.21/2.40    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 2.21/2.40  thf('0', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40              (k1_tops_1 @ sk_A @ sk_B)))
% 2.21/2.40        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('1', plain,
% 2.21/2.40      (~
% 2.21/2.40       (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.21/2.40       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('split', [status(esa)], ['0'])).
% 2.21/2.40  thf('2', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B)))
% 2.21/2.40        | (v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('3', plain,
% 2.21/2.40      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('split', [status(esa)], ['2'])).
% 2.21/2.40  thf('4', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf(t52_pre_topc, axiom,
% 2.21/2.40    (![A:$i]:
% 2.21/2.40     ( ( l1_pre_topc @ A ) =>
% 2.21/2.40       ( ![B:$i]:
% 2.21/2.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.21/2.40           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 2.21/2.40             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 2.21/2.40               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.21/2.40  thf('5', plain,
% 2.21/2.40      (![X26 : $i, X27 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.21/2.40          | ~ (v4_pre_topc @ X26 @ X27)
% 2.21/2.40          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 2.21/2.40          | ~ (l1_pre_topc @ X27))),
% 2.21/2.40      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.21/2.40  thf('6', plain,
% 2.21/2.40      ((~ (l1_pre_topc @ sk_A)
% 2.21/2.40        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 2.21/2.40        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('sup-', [status(thm)], ['4', '5'])).
% 2.21/2.40  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('8', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('demod', [status(thm)], ['6', '7'])).
% 2.21/2.40  thf('9', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('10', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf(dt_k2_pre_topc, axiom,
% 2.21/2.40    (![A:$i,B:$i]:
% 2.21/2.40     ( ( ( l1_pre_topc @ A ) & 
% 2.21/2.40         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.21/2.40       ( m1_subset_1 @
% 2.21/2.40         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.21/2.40  thf('11', plain,
% 2.21/2.40      (![X22 : $i, X23 : $i]:
% 2.21/2.40         (~ (l1_pre_topc @ X22)
% 2.21/2.40          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.21/2.40          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 2.21/2.40             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 2.21/2.40      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.21/2.40  thf('12', plain,
% 2.21/2.40      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.21/2.40        | ~ (l1_pre_topc @ sk_A))),
% 2.21/2.40      inference('sup-', [status(thm)], ['10', '11'])).
% 2.21/2.40  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('14', plain,
% 2.21/2.40      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('demod', [status(thm)], ['12', '13'])).
% 2.21/2.40  thf('15', plain,
% 2.21/2.40      (![X22 : $i, X23 : $i]:
% 2.21/2.40         (~ (l1_pre_topc @ X22)
% 2.21/2.40          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 2.21/2.40          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 2.21/2.40             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 2.21/2.40      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.21/2.40  thf('16', plain,
% 2.21/2.40      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 2.21/2.40         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.21/2.40        | ~ (l1_pre_topc @ sk_A))),
% 2.21/2.40      inference('sup-', [status(thm)], ['14', '15'])).
% 2.21/2.40  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('18', plain,
% 2.21/2.40      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 2.21/2.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('demod', [status(thm)], ['16', '17'])).
% 2.21/2.40  thf(l78_tops_1, axiom,
% 2.21/2.40    (![A:$i]:
% 2.21/2.40     ( ( l1_pre_topc @ A ) =>
% 2.21/2.40       ( ![B:$i]:
% 2.21/2.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.21/2.40           ( ( k2_tops_1 @ A @ B ) =
% 2.21/2.40             ( k7_subset_1 @
% 2.21/2.40               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.21/2.40               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.21/2.40  thf('19', plain,
% 2.21/2.40      (![X28 : $i, X29 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.21/2.40          | ((k2_tops_1 @ X29 @ X28)
% 2.21/2.40              = (k7_subset_1 @ (u1_struct_0 @ X29) @ 
% 2.21/2.40                 (k2_pre_topc @ X29 @ X28) @ (k1_tops_1 @ X29 @ X28)))
% 2.21/2.40          | ~ (l1_pre_topc @ X29))),
% 2.21/2.40      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.21/2.40  thf('20', plain,
% 2.21/2.40      ((~ (l1_pre_topc @ sk_A)
% 2.21/2.40        | ((k2_tops_1 @ sk_A @ 
% 2.21/2.40            (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 2.21/2.40            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.40               (k2_pre_topc @ sk_A @ 
% 2.21/2.40                (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 2.21/2.40               (k1_tops_1 @ sk_A @ 
% 2.21/2.40                (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))))),
% 2.21/2.40      inference('sup-', [status(thm)], ['18', '19'])).
% 2.21/2.40  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('22', plain,
% 2.21/2.40      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 2.21/2.40         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.40            (k2_pre_topc @ sk_A @ 
% 2.21/2.40             (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 2.21/2.40            (k1_tops_1 @ sk_A @ 
% 2.21/2.40             (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('demod', [status(thm)], ['20', '21'])).
% 2.21/2.40  thf('23', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.40             (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ 
% 2.21/2.40              (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup+', [status(thm)], ['9', '22'])).
% 2.21/2.40  thf('24', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('25', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('26', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('27', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('28', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('29', plain,
% 2.21/2.40      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['3', '8'])).
% 2.21/2.40  thf('30', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf(redefinition_k7_subset_1, axiom,
% 2.21/2.40    (![A:$i,B:$i,C:$i]:
% 2.21/2.40     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.21/2.40       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.21/2.40  thf('31', plain,
% 2.21/2.40      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 2.21/2.40          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 2.21/2.40      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.21/2.40  thf('32', plain,
% 2.21/2.40      (![X0 : $i]:
% 2.21/2.40         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.21/2.40           = (k4_xboole_0 @ sk_B @ X0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['30', '31'])).
% 2.21/2.40  thf('33', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.21/2.40         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('demod', [status(thm)],
% 2.21/2.40                ['23', '24', '25', '26', '27', '28', '29', '32'])).
% 2.21/2.40  thf('34', plain,
% 2.21/2.40      (![X0 : $i]:
% 2.21/2.40         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.21/2.40           = (k4_xboole_0 @ sk_B @ X0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['30', '31'])).
% 2.21/2.40  thf('35', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40              (k1_tops_1 @ sk_A @ sk_B))))
% 2.21/2.40         <= (~
% 2.21/2.40             (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('split', [status(esa)], ['0'])).
% 2.21/2.40  thf('36', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.21/2.40         <= (~
% 2.21/2.40             (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('sup-', [status(thm)], ['34', '35'])).
% 2.21/2.40  thf('37', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.21/2.40         <= (~
% 2.21/2.40             (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 2.21/2.40             ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['33', '36'])).
% 2.21/2.40  thf('38', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.21/2.40       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('simplify', [status(thm)], ['37'])).
% 2.21/2.40  thf('39', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.21/2.40       ((v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('split', [status(esa)], ['2'])).
% 2.21/2.40  thf('40', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf(t48_pre_topc, axiom,
% 2.21/2.40    (![A:$i]:
% 2.21/2.40     ( ( l1_pre_topc @ A ) =>
% 2.21/2.40       ( ![B:$i]:
% 2.21/2.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.21/2.40           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 2.21/2.40  thf('41', plain,
% 2.21/2.40      (![X24 : $i, X25 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 2.21/2.40          | (r1_tarski @ X24 @ (k2_pre_topc @ X25 @ X24))
% 2.21/2.40          | ~ (l1_pre_topc @ X25))),
% 2.21/2.40      inference('cnf', [status(esa)], [t48_pre_topc])).
% 2.21/2.40  thf('42', plain,
% 2.21/2.40      ((~ (l1_pre_topc @ sk_A)
% 2.21/2.40        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.21/2.40      inference('sup-', [status(thm)], ['40', '41'])).
% 2.21/2.40  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('44', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 2.21/2.40      inference('demod', [status(thm)], ['42', '43'])).
% 2.21/2.40  thf('45', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf(t44_tops_1, axiom,
% 2.21/2.40    (![A:$i]:
% 2.21/2.40     ( ( l1_pre_topc @ A ) =>
% 2.21/2.40       ( ![B:$i]:
% 2.21/2.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.21/2.40           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.21/2.40  thf('46', plain,
% 2.21/2.40      (![X30 : $i, X31 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.21/2.40          | (r1_tarski @ (k1_tops_1 @ X31 @ X30) @ X30)
% 2.21/2.40          | ~ (l1_pre_topc @ X31))),
% 2.21/2.40      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.21/2.40  thf('47', plain,
% 2.21/2.40      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.21/2.40      inference('sup-', [status(thm)], ['45', '46'])).
% 2.21/2.40  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('49', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.21/2.40      inference('demod', [status(thm)], ['47', '48'])).
% 2.21/2.40  thf(t12_xboole_1, axiom,
% 2.21/2.40    (![A:$i,B:$i]:
% 2.21/2.40     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.21/2.40  thf('50', plain,
% 2.21/2.40      (![X8 : $i, X9 : $i]:
% 2.21/2.40         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 2.21/2.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.21/2.40  thf('51', plain,
% 2.21/2.40      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 2.21/2.40      inference('sup-', [status(thm)], ['49', '50'])).
% 2.21/2.40  thf(t11_xboole_1, axiom,
% 2.21/2.40    (![A:$i,B:$i,C:$i]:
% 2.21/2.40     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.21/2.40  thf('52', plain,
% 2.21/2.40      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.21/2.40         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 2.21/2.40      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.21/2.40  thf('53', plain,
% 2.21/2.40      (![X0 : $i]:
% 2.21/2.40         (~ (r1_tarski @ sk_B @ X0)
% 2.21/2.40          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['51', '52'])).
% 2.21/2.40  thf('54', plain,
% 2.21/2.40      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))),
% 2.21/2.40      inference('sup-', [status(thm)], ['44', '53'])).
% 2.21/2.40  thf(l32_xboole_1, axiom,
% 2.21/2.40    (![A:$i,B:$i]:
% 2.21/2.40     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.21/2.40  thf('55', plain,
% 2.21/2.40      (![X2 : $i, X4 : $i]:
% 2.21/2.40         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 2.21/2.40      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.21/2.40  thf('56', plain,
% 2.21/2.40      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 2.21/2.40         = (k1_xboole_0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['54', '55'])).
% 2.21/2.40  thf(t48_xboole_1, axiom,
% 2.21/2.40    (![A:$i,B:$i]:
% 2.21/2.40     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.21/2.40  thf('57', plain,
% 2.21/2.40      (![X13 : $i, X14 : $i]:
% 2.21/2.40         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.21/2.40           = (k3_xboole_0 @ X13 @ X14))),
% 2.21/2.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.40  thf('58', plain,
% 2.21/2.40      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 2.21/2.40         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.21/2.40            (k2_pre_topc @ sk_A @ sk_B)))),
% 2.21/2.40      inference('sup+', [status(thm)], ['56', '57'])).
% 2.21/2.40  thf(t3_boole, axiom,
% 2.21/2.40    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.21/2.40  thf('59', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.21/2.40      inference('cnf', [status(esa)], [t3_boole])).
% 2.21/2.40  thf(commutativity_k3_xboole_0, axiom,
% 2.21/2.40    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.21/2.40  thf('60', plain,
% 2.21/2.40      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.21/2.40      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.40  thf('61', plain,
% 2.21/2.40      (((k1_tops_1 @ sk_A @ sk_B)
% 2.21/2.40         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.21/2.40      inference('demod', [status(thm)], ['58', '59', '60'])).
% 2.21/2.40  thf('62', plain,
% 2.21/2.40      (![X13 : $i, X14 : $i]:
% 2.21/2.40         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.21/2.40           = (k3_xboole_0 @ X13 @ X14))),
% 2.21/2.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.40  thf(t98_xboole_1, axiom,
% 2.21/2.40    (![A:$i,B:$i]:
% 2.21/2.40     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.21/2.40  thf('63', plain,
% 2.21/2.40      (![X15 : $i, X16 : $i]:
% 2.21/2.40         ((k2_xboole_0 @ X15 @ X16)
% 2.21/2.40           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 2.21/2.40      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.21/2.40  thf('64', plain,
% 2.21/2.40      (![X0 : $i, X1 : $i]:
% 2.21/2.40         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 2.21/2.40           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.21/2.40      inference('sup+', [status(thm)], ['62', '63'])).
% 2.21/2.40  thf(t36_xboole_1, axiom,
% 2.21/2.40    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.21/2.40  thf('65', plain,
% 2.21/2.40      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 2.21/2.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.21/2.40  thf('66', plain,
% 2.21/2.40      (![X8 : $i, X9 : $i]:
% 2.21/2.40         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 2.21/2.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.21/2.40  thf('67', plain,
% 2.21/2.40      (![X0 : $i, X1 : $i]:
% 2.21/2.40         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['65', '66'])).
% 2.21/2.40  thf('68', plain,
% 2.21/2.40      (![X0 : $i, X1 : $i]:
% 2.21/2.40         ((X1)
% 2.21/2.40           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.21/2.40      inference('demod', [status(thm)], ['64', '67'])).
% 2.21/2.40  thf('69', plain,
% 2.21/2.40      (((k2_pre_topc @ sk_A @ sk_B)
% 2.21/2.40         = (k5_xboole_0 @ 
% 2.21/2.40            (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B)) @ 
% 2.21/2.40            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.21/2.40      inference('sup+', [status(thm)], ['61', '68'])).
% 2.21/2.40  thf('70', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('71', plain,
% 2.21/2.40      (![X28 : $i, X29 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.21/2.40          | ((k2_tops_1 @ X29 @ X28)
% 2.21/2.40              = (k7_subset_1 @ (u1_struct_0 @ X29) @ 
% 2.21/2.40                 (k2_pre_topc @ X29 @ X28) @ (k1_tops_1 @ X29 @ X28)))
% 2.21/2.40          | ~ (l1_pre_topc @ X29))),
% 2.21/2.40      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.21/2.40  thf('72', plain,
% 2.21/2.40      ((~ (l1_pre_topc @ sk_A)
% 2.21/2.40        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.40               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.21/2.40      inference('sup-', [status(thm)], ['70', '71'])).
% 2.21/2.40  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('74', plain,
% 2.21/2.40      (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.21/2.40      inference('demod', [status(thm)], ['72', '73'])).
% 2.21/2.40  thf('75', plain,
% 2.21/2.40      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('demod', [status(thm)], ['12', '13'])).
% 2.21/2.40  thf('76', plain,
% 2.21/2.40      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 2.21/2.40          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 2.21/2.40      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.21/2.40  thf('77', plain,
% 2.21/2.40      (![X0 : $i]:
% 2.21/2.40         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['75', '76'])).
% 2.21/2.40  thf('78', plain,
% 2.21/2.40      (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.21/2.40            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.21/2.40      inference('demod', [status(thm)], ['74', '77'])).
% 2.21/2.40  thf('79', plain,
% 2.21/2.40      (((k2_pre_topc @ sk_A @ sk_B)
% 2.21/2.40         = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.21/2.40      inference('demod', [status(thm)], ['69', '78'])).
% 2.21/2.40  thf('80', plain,
% 2.21/2.40      (![X0 : $i]:
% 2.21/2.40         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.21/2.40           = (k4_xboole_0 @ sk_B @ X0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['30', '31'])).
% 2.21/2.40  thf('81', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B))))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('split', [status(esa)], ['2'])).
% 2.21/2.40  thf('82', plain,
% 2.21/2.40      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('sup+', [status(thm)], ['80', '81'])).
% 2.21/2.40  thf('83', plain,
% 2.21/2.40      (![X0 : $i, X1 : $i]:
% 2.21/2.40         ((X1)
% 2.21/2.40           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.21/2.40      inference('demod', [status(thm)], ['64', '67'])).
% 2.21/2.40  thf('84', plain,
% 2.21/2.40      ((((sk_B)
% 2.21/2.40          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.21/2.40             (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('sup+', [status(thm)], ['82', '83'])).
% 2.21/2.40  thf('85', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.21/2.40      inference('demod', [status(thm)], ['47', '48'])).
% 2.21/2.40  thf('86', plain,
% 2.21/2.40      (![X2 : $i, X4 : $i]:
% 2.21/2.40         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 2.21/2.40      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.21/2.40  thf('87', plain,
% 2.21/2.40      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 2.21/2.40      inference('sup-', [status(thm)], ['85', '86'])).
% 2.21/2.40  thf('88', plain,
% 2.21/2.40      (![X13 : $i, X14 : $i]:
% 2.21/2.40         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.21/2.40           = (k3_xboole_0 @ X13 @ X14))),
% 2.21/2.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.40  thf('89', plain,
% 2.21/2.40      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 2.21/2.40         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.21/2.40      inference('sup+', [status(thm)], ['87', '88'])).
% 2.21/2.40  thf('90', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 2.21/2.40      inference('cnf', [status(esa)], [t3_boole])).
% 2.21/2.40  thf('91', plain,
% 2.21/2.40      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.21/2.40      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.40  thf('92', plain,
% 2.21/2.40      (((k1_tops_1 @ sk_A @ sk_B)
% 2.21/2.40         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.21/2.40      inference('demod', [status(thm)], ['89', '90', '91'])).
% 2.21/2.40  thf('93', plain,
% 2.21/2.40      ((((sk_B)
% 2.21/2.40          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B))))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('demod', [status(thm)], ['84', '92'])).
% 2.21/2.40  thf('94', plain,
% 2.21/2.40      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('sup+', [status(thm)], ['79', '93'])).
% 2.21/2.40  thf('95', plain,
% 2.21/2.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('96', plain,
% 2.21/2.40      (![X26 : $i, X27 : $i]:
% 2.21/2.40         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.21/2.40          | ~ (v2_pre_topc @ X27)
% 2.21/2.40          | ((k2_pre_topc @ X27 @ X26) != (X26))
% 2.21/2.40          | (v4_pre_topc @ X26 @ X27)
% 2.21/2.40          | ~ (l1_pre_topc @ X27))),
% 2.21/2.40      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.21/2.40  thf('97', plain,
% 2.21/2.40      ((~ (l1_pre_topc @ sk_A)
% 2.21/2.40        | (v4_pre_topc @ sk_B @ sk_A)
% 2.21/2.40        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 2.21/2.40        | ~ (v2_pre_topc @ sk_A))),
% 2.21/2.40      inference('sup-', [status(thm)], ['95', '96'])).
% 2.21/2.40  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 2.21/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.40  thf('100', plain,
% 2.21/2.40      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 2.21/2.40      inference('demod', [status(thm)], ['97', '98', '99'])).
% 2.21/2.40  thf('101', plain,
% 2.21/2.40      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('sup-', [status(thm)], ['94', '100'])).
% 2.21/2.40  thf('102', plain,
% 2.21/2.40      (((v4_pre_topc @ sk_B @ sk_A))
% 2.21/2.40         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.21/2.40      inference('simplify', [status(thm)], ['101'])).
% 2.21/2.40  thf('103', plain,
% 2.21/2.40      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.21/2.40      inference('split', [status(esa)], ['0'])).
% 2.21/2.40  thf('104', plain,
% 2.21/2.40      (~
% 2.21/2.40       (((k2_tops_1 @ sk_A @ sk_B)
% 2.21/2.40          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.21/2.40             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.21/2.40       ((v4_pre_topc @ sk_B @ sk_A))),
% 2.21/2.40      inference('sup-', [status(thm)], ['102', '103'])).
% 2.21/2.40  thf('105', plain, ($false),
% 2.21/2.40      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '104'])).
% 2.21/2.40  
% 2.21/2.40  % SZS output end Refutation
% 2.21/2.40  
% 2.21/2.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
