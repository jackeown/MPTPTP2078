%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d8vg3E5xlh

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 140 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  710 (1333 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X17 @ ( k2_pre_topc @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X24 @ X23 ) @ ( k2_tops_1 @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d8vg3E5xlh
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 90 iterations in 0.041s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.19/0.49  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(t88_tops_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( ( v2_tops_1 @ B @ A ) <=>
% 0.19/0.49             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( l1_pre_topc @ A ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49              ( ( v2_tops_1 @ B @ A ) <=>
% 0.19/0.49                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.49        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.19/0.49       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.49        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t84_tops_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( ( v2_tops_1 @ B @ A ) <=>
% 0.19/0.49             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X25 : $i, X26 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.19/0.49          | ~ (v2_tops_1 @ X25 @ X26)
% 0.19/0.49          | ((k1_tops_1 @ X26 @ X25) = (k1_xboole_0))
% 0.19/0.49          | ~ (l1_pre_topc @ X26))),
% 0.19/0.49      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.19/0.49        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.19/0.49        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.19/0.49         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(l78_tops_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.49             ( k7_subset_1 @
% 0.19/0.49               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.19/0.49               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.49          | ((k2_tops_1 @ X20 @ X19)
% 0.19/0.49              = (k7_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.19/0.49                 (k2_pre_topc @ X20 @ X19) @ (k1_tops_1 @ X20 @ X19)))
% 0.19/0.49          | ~ (l1_pre_topc @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_k2_pre_topc, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.49       ( m1_subset_1 @
% 0.19/0.49         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i]:
% 0.19/0.49         (~ (l1_pre_topc @ X15)
% 0.19/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.49          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.19/0.49          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.49           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.49         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.49            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['12', '13', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.49          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)))
% 0.19/0.49         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['9', '21'])).
% 0.19/0.49  thf(t3_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('23', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.19/0.49         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t48_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.49          | (r1_tarski @ X17 @ (k2_pre_topc @ X18 @ X17))
% 0.19/0.49          | ~ (l1_pre_topc @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('29', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['24', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.19/0.49       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.19/0.49       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t73_tops_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.49          | (r1_xboole_0 @ (k1_tops_1 @ X24 @ X23) @ (k2_tops_1 @ X24 @ X23))
% 0.19/0.49          | ~ (l1_pre_topc @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t73_tops_1])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      ((r1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf(t63_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.19/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X6 @ X7)
% 0.19/0.49          | ~ (r1_xboole_0 @ X7 @ X8)
% 0.19/0.49          | (r1_xboole_0 @ X6 @ X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          ((r1_xboole_0 @ sk_B @ X0)
% 0.19/0.49           | ~ (r1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (((r1_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['40', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf(t83_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      ((((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.19/0.49          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t44_tops_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.49          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 0.19/0.49          | ~ (l1_pre_topc @ X22))),
% 0.19/0.49      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('53', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.49  thf(l32_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (![X2 : $i, X4 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['48', '55'])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (![X25 : $i, X26 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.19/0.49          | ((k1_tops_1 @ X26 @ X25) != (k1_xboole_0))
% 0.19/0.49          | (v2_tops_1 @ X25 @ X26)
% 0.19/0.49          | ~ (l1_pre_topc @ X26))),
% 0.19/0.49      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.49        | (v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.49        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.49  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (((v2_tops_1 @ sk_B @ sk_A)
% 0.19/0.49        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.49  thf('62', plain,
% 0.19/0.49      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['56', '61'])).
% 0.19/0.49  thf('63', plain,
% 0.19/0.49      (((v2_tops_1 @ sk_B @ sk_A))
% 0.19/0.49         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.49  thf('64', plain,
% 0.19/0.49      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('65', plain,
% 0.19/0.49      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.19/0.49       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.49  thf('66', plain, ($false),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '65'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
