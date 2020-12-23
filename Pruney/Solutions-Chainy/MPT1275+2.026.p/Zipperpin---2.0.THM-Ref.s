%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hOdS5lnl56

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 245 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  794 (2694 expanded)
%              Number of equality atoms :   48 ( 156 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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

thf('0',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tops_1 @ X27 @ X28 )
      | ~ ( v3_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( r1_tarski @ X25 @ ( k2_tops_1 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k7_subset_1 @ X8 @ X7 @ X9 )
        = ( k4_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','32','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('43',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('52',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( sk_B
     != ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
   <= ( ( sk_B
       != ( k2_tops_1 @ sk_A @ sk_B ) )
      & ( v3_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k2_tops_1 @ sk_A @ sk_B ) )
      & ( v3_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ ( k2_tops_1 @ X26 @ X25 ) )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X20 @ X19 ) @ X20 )
      | ( v3_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('72',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','55','56','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hOdS5lnl56
% 0.13/0.36  % Computer   : n005.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:46:03 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 155 iterations in 0.078s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.22/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.22/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(t94_tops_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v4_pre_topc @ B @ A ) =>
% 0.22/0.55             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( l1_pre_topc @ A ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55              ( ( v4_pre_topc @ B @ A ) =>
% 0.22/0.55                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t92_tops_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X27 : $i, X28 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.22/0.55          | (v2_tops_1 @ X27 @ X28)
% 0.22/0.55          | ~ (v3_tops_1 @ X27 @ X28)
% 0.22/0.55          | ~ (l1_pre_topc @ X28))),
% 0.22/0.55      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.22/0.55        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t88_tops_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.55             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X25 : $i, X26 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.22/0.55          | ~ (v2_tops_1 @ X25 @ X26)
% 0.22/0.55          | (r1_tarski @ X25 @ (k2_tops_1 @ X26 @ X25))
% 0.22/0.55          | ~ (l1_pre_topc @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t84_tops_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.55             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.55          | ~ (v2_tops_1 @ X23 @ X24)
% 0.22/0.55          | ((k1_tops_1 @ X24 @ X23) = (k1_xboole_0))
% 0.22/0.55          | ~ (l1_pre_topc @ X24))),
% 0.22/0.55      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.55        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['16', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(l78_tops_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.55             ( k7_subset_1 @
% 0.22/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.22/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X21 : $i, X22 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.55          | ((k2_tops_1 @ X22 @ X21)
% 0.22/0.55              = (k7_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.22/0.55                 (k2_pre_topc @ X22 @ X21) @ (k1_tops_1 @ X22 @ X21)))
% 0.22/0.55          | ~ (l1_pre_topc @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t52_pre_topc, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X17 : $i, X18 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.55          | ~ (v4_pre_topc @ X17 @ X18)
% 0.22/0.55          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.22/0.55          | ~ (l1_pre_topc @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.22/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('31', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('32', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.55          | ((k7_subset_1 @ X8 @ X7 @ X9) = (k4_xboole_0 @ X7 @ X9)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.22/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.55         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['25', '26', '32', '35'])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      ((((k2_tops_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['22', '36'])).
% 0.22/0.55  thf(t4_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(d5_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.22/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      ((((k2_tops_1 @ sk_A @ sk_B) = (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['37', '40'])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['15', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(dt_k3_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 0.22/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.55  thf(t3_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i]:
% 0.22/0.55         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf(d10_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (![X0 : $i, X2 : $i]:
% 0.22/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.22/0.55          | ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      ((((sk_B) = (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['42', '49'])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      ((((k2_tops_1 @ sk_A @ sk_B) = (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.22/0.55         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['37', '40'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      ((((sk_B) != (k3_subset_1 @ sk_B @ k1_xboole_0)))
% 0.22/0.55         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) & 
% 0.22/0.55             ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      ((((sk_B) != (sk_B)))
% 0.22/0.55         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) & 
% 0.22/0.55             ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ((v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.55         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['2'])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X25 : $i, X26 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.22/0.55          | ~ (r1_tarski @ X25 @ (k2_tops_1 @ X26 @ X25))
% 0.22/0.55          | (v2_tops_1 @ X25 @ X26)
% 0.22/0.55          | ~ (l1_pre_topc @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.55        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (((v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.55        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.22/0.55         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['57', '62'])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('65', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.55      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['63', '65'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d5_tops_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v3_tops_1 @ B @ A ) <=>
% 0.22/0.55             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (![X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.55          | ~ (v2_tops_1 @ (k2_pre_topc @ X20 @ X19) @ X20)
% 0.22/0.55          | (v3_tops_1 @ X19 @ X20)
% 0.22/0.55          | ~ (l1_pre_topc @ X20))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | (v3_tops_1 @ sk_B @ sk_A)
% 0.22/0.55        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('71', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.55  thf('72', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['66', '72'])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ((v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.55  thf('76', plain, ($false),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['1', '55', '56', '75'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
