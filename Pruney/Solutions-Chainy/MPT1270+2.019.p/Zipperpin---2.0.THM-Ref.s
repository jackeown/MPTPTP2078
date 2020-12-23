%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VLgvc4ZngJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 146 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  746 (1387 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tops_1 @ X24 @ X25 )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','20'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ X16 @ ( k2_pre_topc @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X23 @ X22 ) @ ( k2_tops_1 @ X23 @ X22 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_xboole_0 @ X8 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('47',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_xboole_0 @ X8 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('59',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('60',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VLgvc4ZngJ
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 112 iterations in 0.052s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(t88_tops_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.52             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( l1_pre_topc @ A ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52              ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.52                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.52        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t84_tops_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.52             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.52          | ~ (v2_tops_1 @ X24 @ X25)
% 0.22/0.52          | ((k1_tops_1 @ X25 @ X24) = (k1_xboole_0))
% 0.22/0.52          | ~ (l1_pre_topc @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.52        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.52        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.52         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(l78_tops_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.52             ( k7_subset_1 @
% 0.22/0.52               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.22/0.52               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.52          | ((k2_tops_1 @ X19 @ X18)
% 0.22/0.52              = (k7_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.22/0.52                 (k2_pre_topc @ X19 @ X18) @ (k1_tops_1 @ X19 @ X18)))
% 0.22/0.52          | ~ (l1_pre_topc @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.52            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k2_pre_topc, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @
% 0.22/0.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X14)
% 0.22/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.52          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.22/0.52          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.52           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.52         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.52            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.52          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)))
% 0.22/0.52         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['9', '21'])).
% 0.22/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.52  thf('23', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf(t83_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.52         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['22', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t48_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.52          | (r1_tarski @ X16 @ (k2_pre_topc @ X17 @ X16))
% 0.22/0.52          | ~ (l1_pre_topc @ X17))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('31', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['26', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t73_tops_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.22/0.52          | (r1_xboole_0 @ (k1_tops_1 @ X23 @ X22) @ (k2_tops_1 @ X23 @ X22))
% 0.22/0.52          | ~ (l1_pre_topc @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [t73_tops_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.22/0.52         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf(t85_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X8 @ X9)
% 0.22/0.52          | (r1_xboole_0 @ X8 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['42', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.52          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t44_tops_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.52          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ X20)
% 0.22/0.52          | ~ (l1_pre_topc @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.52  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('55', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X8 @ X9)
% 0.22/0.52          | (r1_xboole_0 @ X8 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['50', '57'])).
% 0.22/0.52  thf(t66_xboole_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.52          | ((k1_tops_1 @ X25 @ X24) != (k1_xboole_0))
% 0.22/0.52          | (v2_tops_1 @ X24 @ X25)
% 0.22/0.52          | ~ (l1_pre_topc @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.52        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.52  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (((v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.52        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['60', '65'])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (((v2_tops_1 @ sk_B @ sk_A))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.52  thf('70', plain, ($false),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['1', '34', '35', '69'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
