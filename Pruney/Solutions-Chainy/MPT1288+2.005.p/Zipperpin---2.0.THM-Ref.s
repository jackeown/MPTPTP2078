%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rKd6t6eejI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:58 EST 2020

% Result     : Theorem 4.52s
% Output     : Refutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 446 expanded)
%              Number of leaves         :   34 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          : 1715 (5806 expanded)
%              Number of equality atoms :   38 ( 207 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ ( k2_tops_1 @ X23 @ ( k2_tops_1 @ X23 @ X22 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('6',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t94_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_tops_1 @ X31 @ X32 )
      | ( X31
        = ( k2_tops_1 @ X32 @ X31 ) )
      | ~ ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('21',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t95_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X34 @ X33 ) @ X34 )
      | ~ ( v3_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t95_tops_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('32',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29','35'])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','24','36'])).

thf('38',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ ( k1_tops_1 @ X24 @ X25 ) )
        = ( k1_tops_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ ( k2_pre_topc @ X6 @ X5 ) @ ( k2_pre_topc @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('61',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('65',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ( r1_tarski @ ( k2_pre_topc @ X27 @ X28 ) @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','87'])).

thf('89',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ( r1_tarski @ ( k2_pre_topc @ X27 @ X28 ) @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('101',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','104'])).

thf('106',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','105'])).

thf('107',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('108',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ ( k2_pre_topc @ X6 @ X5 ) @ ( k2_pre_topc @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_tops_1 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ ( k1_tops_1 @ X9 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','123'])).

thf('125',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('127',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','125','126'])).

thf('128',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','127'])).

thf('129',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['129','134'])).

thf('136',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','135'])).

thf('137',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rKd6t6eejI
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.52/4.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.52/4.72  % Solved by: fo/fo7.sh
% 4.52/4.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.52/4.72  % done 4629 iterations in 4.265s
% 4.52/4.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.52/4.72  % SZS output start Refutation
% 4.52/4.72  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.52/4.72  thf(sk_B_type, type, sk_B: $i).
% 4.52/4.72  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 4.52/4.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.52/4.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.52/4.72  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.52/4.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.52/4.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.52/4.72  thf(sk_A_type, type, sk_A: $i).
% 4.52/4.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.52/4.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.52/4.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.52/4.72  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 4.52/4.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.52/4.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.52/4.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.52/4.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.52/4.72  thf(t110_tops_1, conjecture,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ( v4_tops_1 @ B @ A ) =>
% 4.52/4.72             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 4.52/4.72  thf(zf_stmt_0, negated_conjecture,
% 4.52/4.72    (~( ![A:$i]:
% 4.52/4.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.52/4.72          ( ![B:$i]:
% 4.52/4.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72              ( ( v4_tops_1 @ B @ A ) =>
% 4.52/4.72                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 4.52/4.72    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 4.52/4.72  thf('0', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf(dt_k1_tops_1, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( m1_subset_1 @
% 4.52/4.72         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.52/4.72  thf('1', plain,
% 4.52/4.72      (![X10 : $i, X11 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X10)
% 4.52/4.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 4.52/4.72          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 4.52/4.72             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 4.52/4.72      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 4.52/4.72  thf('2', plain,
% 4.52/4.72      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['0', '1'])).
% 4.52/4.72  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('4', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(l80_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 4.52/4.72             ( k1_xboole_0 ) ) ) ) ))).
% 4.52/4.72  thf('5', plain,
% 4.52/4.72      (![X22 : $i, X23 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 4.52/4.72          | ((k1_tops_1 @ X23 @ (k2_tops_1 @ X23 @ (k2_tops_1 @ X23 @ X22)))
% 4.52/4.72              = (k1_xboole_0))
% 4.52/4.72          | ~ (l1_pre_topc @ X23)
% 4.52/4.72          | ~ (v2_pre_topc @ X23))),
% 4.52/4.72      inference('cnf', [status(esa)], [l80_tops_1])).
% 4.52/4.72  thf('6', plain,
% 4.52/4.72      ((~ (v2_pre_topc @ sk_A)
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A)
% 4.52/4.72        | ((k1_tops_1 @ sk_A @ 
% 4.52/4.72            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 4.52/4.72            = (k1_xboole_0)))),
% 4.52/4.72      inference('sup-', [status(thm)], ['4', '5'])).
% 4.52/4.72  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('9', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ 
% 4.52/4.72         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 4.52/4.72         = (k1_xboole_0))),
% 4.52/4.72      inference('demod', [status(thm)], ['6', '7', '8'])).
% 4.52/4.72  thf('10', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(dt_k2_tops_1, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( m1_subset_1 @
% 4.52/4.72         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.52/4.72  thf('11', plain,
% 4.52/4.72      (![X12 : $i, X13 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X12)
% 4.52/4.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 4.52/4.72          | (m1_subset_1 @ (k2_tops_1 @ X12 @ X13) @ 
% 4.52/4.72             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 4.52/4.72      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 4.52/4.72  thf('12', plain,
% 4.52/4.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['10', '11'])).
% 4.52/4.72  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('14', plain,
% 4.52/4.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['12', '13'])).
% 4.52/4.72  thf(t94_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( l1_pre_topc @ A ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ( v4_pre_topc @ B @ A ) =>
% 4.52/4.72             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 4.52/4.72  thf('15', plain,
% 4.52/4.72      (![X31 : $i, X32 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 4.52/4.72          | ~ (v3_tops_1 @ X31 @ X32)
% 4.52/4.72          | ((X31) = (k2_tops_1 @ X32 @ X31))
% 4.52/4.72          | ~ (v4_pre_topc @ X31 @ X32)
% 4.52/4.72          | ~ (l1_pre_topc @ X32))),
% 4.52/4.72      inference('cnf', [status(esa)], [t94_tops_1])).
% 4.52/4.72  thf('16', plain,
% 4.52/4.72      ((~ (l1_pre_topc @ sk_A)
% 4.52/4.72        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72             sk_A)
% 4.52/4.72        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72            = (k2_tops_1 @ sk_A @ 
% 4.52/4.72               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 4.52/4.72        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['14', '15'])).
% 4.52/4.72  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('18', plain,
% 4.52/4.72      ((~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 4.52/4.72        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72            = (k2_tops_1 @ sk_A @ 
% 4.52/4.72               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 4.52/4.72        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 4.52/4.72      inference('demod', [status(thm)], ['16', '17'])).
% 4.52/4.72  thf('19', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(fc11_tops_1, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 4.52/4.72  thf('20', plain,
% 4.52/4.72      (![X14 : $i, X15 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X14)
% 4.52/4.72          | ~ (v2_pre_topc @ X14)
% 4.52/4.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 4.52/4.72          | (v4_pre_topc @ (k2_tops_1 @ X14 @ X15) @ X14))),
% 4.52/4.72      inference('cnf', [status(esa)], [fc11_tops_1])).
% 4.52/4.72  thf('21', plain,
% 4.52/4.72      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 4.52/4.72        | ~ (v2_pre_topc @ sk_A)
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['19', '20'])).
% 4.52/4.72  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('24', plain,
% 4.52/4.72      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 4.52/4.72      inference('demod', [status(thm)], ['21', '22', '23'])).
% 4.52/4.72  thf('25', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(t95_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ( v3_pre_topc @ B @ A ) =>
% 4.52/4.72             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 4.52/4.72  thf('26', plain,
% 4.52/4.72      (![X33 : $i, X34 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 4.52/4.72          | (v3_tops_1 @ (k2_tops_1 @ X34 @ X33) @ X34)
% 4.52/4.72          | ~ (v3_pre_topc @ X33 @ X34)
% 4.52/4.72          | ~ (l1_pre_topc @ X34)
% 4.52/4.72          | ~ (v2_pre_topc @ X34))),
% 4.52/4.72      inference('cnf', [status(esa)], [t95_tops_1])).
% 4.52/4.72  thf('27', plain,
% 4.52/4.72      ((~ (v2_pre_topc @ sk_A)
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A)
% 4.52/4.72        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.52/4.72        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['25', '26'])).
% 4.52/4.72  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('30', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf(fc9_tops_1, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.52/4.72  thf('31', plain,
% 4.52/4.72      (![X18 : $i, X19 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X18)
% 4.52/4.72          | ~ (v2_pre_topc @ X18)
% 4.52/4.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.52/4.72          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 4.52/4.72      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.52/4.72  thf('32', plain,
% 4.52/4.72      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.52/4.72        | ~ (v2_pre_topc @ sk_A)
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['30', '31'])).
% 4.52/4.72  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('35', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.52/4.72      inference('demod', [status(thm)], ['32', '33', '34'])).
% 4.52/4.72  thf('36', plain,
% 4.52/4.72      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 4.52/4.72      inference('demod', [status(thm)], ['27', '28', '29', '35'])).
% 4.52/4.72  thf('37', plain,
% 4.52/4.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('demod', [status(thm)], ['18', '24', '36'])).
% 4.52/4.72  thf('38', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72         = (k1_xboole_0))),
% 4.52/4.72      inference('demod', [status(thm)], ['9', '37'])).
% 4.52/4.72  thf('39', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(l78_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( l1_pre_topc @ A ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ( k2_tops_1 @ A @ B ) =
% 4.52/4.72             ( k7_subset_1 @
% 4.52/4.72               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 4.52/4.72               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.52/4.72  thf('40', plain,
% 4.52/4.72      (![X20 : $i, X21 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 4.52/4.72          | ((k2_tops_1 @ X21 @ X20)
% 4.52/4.72              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 4.52/4.72                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 4.52/4.72          | ~ (l1_pre_topc @ X21))),
% 4.52/4.72      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.52/4.72  thf('41', plain,
% 4.52/4.72      ((~ (l1_pre_topc @ sk_A)
% 4.52/4.72        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.52/4.72               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 4.52/4.72      inference('sup-', [status(thm)], ['39', '40'])).
% 4.52/4.72  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('43', plain,
% 4.52/4.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.52/4.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72            (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('demod', [status(thm)], ['41', '42'])).
% 4.52/4.72  thf('44', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf(projectivity_k1_tops_1, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 4.52/4.72  thf('45', plain,
% 4.52/4.72      (![X24 : $i, X25 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X24)
% 4.52/4.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 4.52/4.72          | ((k1_tops_1 @ X24 @ (k1_tops_1 @ X24 @ X25))
% 4.52/4.72              = (k1_tops_1 @ X24 @ X25)))),
% 4.52/4.72      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 4.52/4.72  thf('46', plain,
% 4.52/4.72      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72          = (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['44', '45'])).
% 4.52/4.72  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('48', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.52/4.72      inference('demod', [status(thm)], ['46', '47'])).
% 4.52/4.72  thf('49', plain,
% 4.52/4.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.52/4.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['43', '48'])).
% 4.52/4.72  thf('50', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('51', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf('52', plain,
% 4.52/4.72      (![X10 : $i, X11 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X10)
% 4.52/4.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 4.52/4.72          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 4.52/4.72             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 4.52/4.72      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 4.52/4.72  thf('53', plain,
% 4.52/4.72      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['51', '52'])).
% 4.52/4.72  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('55', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['53', '54'])).
% 4.52/4.72  thf(t49_pre_topc, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( l1_pre_topc @ A ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ![C:$i]:
% 4.52/4.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72               ( ( r1_tarski @ B @ C ) =>
% 4.52/4.72                 ( r1_tarski @
% 4.52/4.72                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 4.52/4.72  thf('56', plain,
% 4.52/4.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 4.52/4.72          | ~ (r1_tarski @ X5 @ X7)
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ X6 @ X5) @ (k2_pre_topc @ X6 @ X7))
% 4.52/4.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 4.52/4.72          | ~ (l1_pre_topc @ X6))),
% 4.52/4.72      inference('cnf', [status(esa)], [t49_pre_topc])).
% 4.52/4.72  thf('57', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ sk_A)
% 4.52/4.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ 
% 4.52/4.72              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ X0))
% 4.52/4.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 4.52/4.72      inference('sup-', [status(thm)], ['55', '56'])).
% 4.52/4.72  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('59', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ 
% 4.52/4.72              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ X0))
% 4.52/4.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 4.52/4.72      inference('demod', [status(thm)], ['57', '58'])).
% 4.52/4.72  thf('60', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.52/4.72      inference('demod', [status(thm)], ['46', '47'])).
% 4.52/4.72  thf('61', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.52/4.72      inference('demod', [status(thm)], ['46', '47'])).
% 4.52/4.72  thf('62', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ X0))
% 4.52/4.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 4.52/4.72      inference('demod', [status(thm)], ['59', '60', '61'])).
% 4.52/4.72  thf('63', plain,
% 4.52/4.72      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 4.52/4.72        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ sk_B)))),
% 4.52/4.72      inference('sup-', [status(thm)], ['50', '62'])).
% 4.52/4.72  thf('64', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf(t44_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( l1_pre_topc @ A ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 4.52/4.72  thf('65', plain,
% 4.52/4.72      (![X29 : $i, X30 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.52/4.72          | (r1_tarski @ (k1_tops_1 @ X30 @ X29) @ X29)
% 4.52/4.72          | ~ (l1_pre_topc @ X30))),
% 4.52/4.72      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.52/4.72  thf('66', plain,
% 4.52/4.72      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 4.52/4.72      inference('sup-', [status(thm)], ['64', '65'])).
% 4.52/4.72  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('68', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.52/4.72      inference('demod', [status(thm)], ['66', '67'])).
% 4.52/4.72  thf('69', plain,
% 4.52/4.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k2_pre_topc @ sk_A @ sk_B))),
% 4.52/4.72      inference('demod', [status(thm)], ['63', '68'])).
% 4.52/4.72  thf(d10_xboole_0, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.52/4.72  thf('70', plain,
% 4.52/4.72      (![X0 : $i, X2 : $i]:
% 4.52/4.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.52/4.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.52/4.72  thf('71', plain,
% 4.52/4.72      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72        | ((k2_pre_topc @ sk_A @ sk_B)
% 4.52/4.72            = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('sup-', [status(thm)], ['69', '70'])).
% 4.52/4.72  thf('72', plain,
% 4.52/4.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.52/4.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.52/4.72  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.52/4.72      inference('simplify', [status(thm)], ['72'])).
% 4.52/4.72  thf('74', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(dt_k2_pre_topc, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( m1_subset_1 @
% 4.52/4.72         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.52/4.72  thf('75', plain,
% 4.52/4.72      (![X3 : $i, X4 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X3)
% 4.52/4.72          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 4.52/4.72          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 4.52/4.72             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 4.52/4.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 4.52/4.72  thf('76', plain,
% 4.52/4.72      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['74', '75'])).
% 4.52/4.72  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('78', plain,
% 4.52/4.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['76', '77'])).
% 4.52/4.72  thf(t31_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( l1_pre_topc @ A ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ![C:$i]:
% 4.52/4.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 4.52/4.72                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 4.52/4.72  thf('79', plain,
% 4.52/4.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 4.52/4.72          | ~ (v4_pre_topc @ X26 @ X27)
% 4.52/4.72          | ~ (r1_tarski @ X28 @ X26)
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ X27 @ X28) @ X26)
% 4.52/4.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 4.52/4.72          | ~ (l1_pre_topc @ X27))),
% 4.52/4.72      inference('cnf', [status(esa)], [t31_tops_1])).
% 4.52/4.72  thf('80', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ sk_A)
% 4.52/4.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72          | ~ (r1_tarski @ X0 @ 
% 4.52/4.72               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72          | ~ (v4_pre_topc @ 
% 4.52/4.72               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['78', '79'])).
% 4.52/4.72  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('82', plain,
% 4.52/4.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['2', '3'])).
% 4.52/4.72  thf(fc1_tops_1, axiom,
% 4.52/4.72    (![A:$i,B:$i]:
% 4.52/4.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.52/4.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.52/4.72       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 4.52/4.72  thf('83', plain,
% 4.52/4.72      (![X16 : $i, X17 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X16)
% 4.52/4.72          | ~ (v2_pre_topc @ X16)
% 4.52/4.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 4.52/4.72          | (v4_pre_topc @ (k2_pre_topc @ X16 @ X17) @ X16))),
% 4.52/4.72      inference('cnf', [status(esa)], [fc1_tops_1])).
% 4.52/4.72  thf('84', plain,
% 4.52/4.72      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 4.52/4.72        | ~ (v2_pre_topc @ sk_A)
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['82', '83'])).
% 4.52/4.72  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('87', plain,
% 4.52/4.72      ((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 4.52/4.72      inference('demod', [status(thm)], ['84', '85', '86'])).
% 4.52/4.72  thf('88', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72          | ~ (r1_tarski @ X0 @ 
% 4.52/4.72               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('demod', [status(thm)], ['80', '81', '87'])).
% 4.52/4.72  thf('89', plain,
% 4.52/4.72      (((r1_tarski @ 
% 4.52/4.72         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 4.52/4.72         (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.52/4.72      inference('sup-', [status(thm)], ['73', '88'])).
% 4.52/4.72  thf('90', plain,
% 4.52/4.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['76', '77'])).
% 4.52/4.72  thf('91', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('92', plain,
% 4.52/4.72      (![X3 : $i, X4 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X3)
% 4.52/4.72          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 4.52/4.72          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 4.52/4.72             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 4.52/4.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 4.52/4.72  thf('93', plain,
% 4.52/4.72      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['91', '92'])).
% 4.52/4.72  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('95', plain,
% 4.52/4.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['93', '94'])).
% 4.52/4.72  thf('96', plain,
% 4.52/4.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 4.52/4.72          | ~ (v4_pre_topc @ X26 @ X27)
% 4.52/4.72          | ~ (r1_tarski @ X28 @ X26)
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ X27 @ X28) @ X26)
% 4.52/4.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 4.52/4.72          | ~ (l1_pre_topc @ X27))),
% 4.52/4.72      inference('cnf', [status(esa)], [t31_tops_1])).
% 4.52/4.72  thf('97', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ sk_A)
% 4.52/4.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ sk_B))
% 4.52/4.72          | ~ (r1_tarski @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 4.52/4.72          | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['95', '96'])).
% 4.52/4.72  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('99', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('100', plain,
% 4.52/4.72      (![X16 : $i, X17 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ X16)
% 4.52/4.72          | ~ (v2_pre_topc @ X16)
% 4.52/4.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 4.52/4.72          | (v4_pre_topc @ (k2_pre_topc @ X16 @ X17) @ X16))),
% 4.52/4.72      inference('cnf', [status(esa)], [fc1_tops_1])).
% 4.52/4.72  thf('101', plain,
% 4.52/4.72      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 4.52/4.72        | ~ (v2_pre_topc @ sk_A)
% 4.52/4.72        | ~ (l1_pre_topc @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['99', '100'])).
% 4.52/4.72  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('104', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 4.52/4.72      inference('demod', [status(thm)], ['101', '102', '103'])).
% 4.52/4.72  thf('105', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ sk_B))
% 4.52/4.72          | ~ (r1_tarski @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['97', '98', '104'])).
% 4.52/4.72  thf('106', plain,
% 4.52/4.72      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ sk_B))
% 4.52/4.72        | (r1_tarski @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ 
% 4.52/4.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ sk_B)))),
% 4.52/4.72      inference('sup-', [status(thm)], ['90', '105'])).
% 4.52/4.72  thf('107', plain,
% 4.52/4.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k2_pre_topc @ sk_A @ sk_B))),
% 4.52/4.72      inference('demod', [status(thm)], ['63', '68'])).
% 4.52/4.72  thf('108', plain,
% 4.52/4.72      ((r1_tarski @ 
% 4.52/4.72        (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 4.52/4.72        (k2_pre_topc @ sk_A @ sk_B))),
% 4.52/4.72      inference('demod', [status(thm)], ['106', '107'])).
% 4.52/4.72  thf('109', plain,
% 4.52/4.72      (![X0 : $i, X2 : $i]:
% 4.52/4.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.52/4.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.52/4.72  thf('110', plain,
% 4.52/4.72      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ 
% 4.52/4.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 4.52/4.72        | ((k2_pre_topc @ sk_A @ sk_B)
% 4.52/4.72            = (k2_pre_topc @ sk_A @ 
% 4.52/4.72               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 4.52/4.72      inference('sup-', [status(thm)], ['108', '109'])).
% 4.52/4.72  thf('111', plain,
% 4.52/4.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['76', '77'])).
% 4.52/4.72  thf('112', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('113', plain,
% 4.52/4.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 4.52/4.72          | ~ (r1_tarski @ X5 @ X7)
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ X6 @ X5) @ (k2_pre_topc @ X6 @ X7))
% 4.52/4.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 4.52/4.72          | ~ (l1_pre_topc @ X6))),
% 4.52/4.72      inference('cnf', [status(esa)], [t49_pre_topc])).
% 4.52/4.72  thf('114', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (l1_pre_topc @ sk_A)
% 4.52/4.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ X0))
% 4.52/4.72          | ~ (r1_tarski @ sk_B @ X0))),
% 4.52/4.72      inference('sup-', [status(thm)], ['112', '113'])).
% 4.52/4.72  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('116', plain,
% 4.52/4.72      (![X0 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.52/4.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72             (k2_pre_topc @ sk_A @ X0))
% 4.52/4.72          | ~ (r1_tarski @ sk_B @ X0))),
% 4.52/4.72      inference('demod', [status(thm)], ['114', '115'])).
% 4.52/4.72  thf('117', plain,
% 4.52/4.72      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72           (k2_pre_topc @ sk_A @ 
% 4.52/4.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 4.52/4.72      inference('sup-', [status(thm)], ['111', '116'])).
% 4.52/4.72  thf('118', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf(d6_tops_1, axiom,
% 4.52/4.72    (![A:$i]:
% 4.52/4.72     ( ( l1_pre_topc @ A ) =>
% 4.52/4.72       ( ![B:$i]:
% 4.52/4.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.52/4.72           ( ( v4_tops_1 @ B @ A ) <=>
% 4.52/4.72             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 4.52/4.72               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 4.52/4.72  thf('119', plain,
% 4.52/4.72      (![X8 : $i, X9 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 4.52/4.72          | ~ (v4_tops_1 @ X8 @ X9)
% 4.52/4.72          | (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ (k1_tops_1 @ X9 @ X8)))
% 4.52/4.72          | ~ (l1_pre_topc @ X9))),
% 4.52/4.72      inference('cnf', [status(esa)], [d6_tops_1])).
% 4.52/4.72  thf('120', plain,
% 4.52/4.72      ((~ (l1_pre_topc @ sk_A)
% 4.52/4.72        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.52/4.72        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 4.52/4.72      inference('sup-', [status(thm)], ['118', '119'])).
% 4.52/4.72  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('122', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('123', plain,
% 4.52/4.72      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['120', '121', '122'])).
% 4.52/4.72  thf('124', plain,
% 4.52/4.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72        (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('demod', [status(thm)], ['117', '123'])).
% 4.52/4.72  thf('125', plain,
% 4.52/4.72      (((k2_pre_topc @ sk_A @ sk_B)
% 4.52/4.72         = (k2_pre_topc @ sk_A @ 
% 4.52/4.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('demod', [status(thm)], ['110', '124'])).
% 4.52/4.72  thf('126', plain,
% 4.52/4.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.52/4.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('demod', [status(thm)], ['76', '77'])).
% 4.52/4.72  thf('127', plain,
% 4.52/4.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['89', '125', '126'])).
% 4.52/4.72  thf('128', plain,
% 4.52/4.72      (((k2_pre_topc @ sk_A @ sk_B)
% 4.52/4.72         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['71', '127'])).
% 4.52/4.72  thf('129', plain,
% 4.52/4.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.52/4.72         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['49', '128'])).
% 4.52/4.72  thf('130', plain,
% 4.52/4.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('131', plain,
% 4.52/4.72      (![X20 : $i, X21 : $i]:
% 4.52/4.72         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 4.52/4.72          | ((k2_tops_1 @ X21 @ X20)
% 4.52/4.72              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 4.52/4.72                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 4.52/4.72          | ~ (l1_pre_topc @ X21))),
% 4.52/4.72      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.52/4.72  thf('132', plain,
% 4.52/4.72      ((~ (l1_pre_topc @ sk_A)
% 4.52/4.72        | ((k2_tops_1 @ sk_A @ sk_B)
% 4.52/4.72            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.52/4.72               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.52/4.72      inference('sup-', [status(thm)], ['130', '131'])).
% 4.52/4.72  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('134', plain,
% 4.52/4.72      (((k2_tops_1 @ sk_A @ sk_B)
% 4.52/4.72         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.52/4.72            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('demod', [status(thm)], ['132', '133'])).
% 4.52/4.72  thf('135', plain,
% 4.52/4.72      (((k2_tops_1 @ sk_A @ sk_B)
% 4.52/4.72         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.52/4.72      inference('sup+', [status(thm)], ['129', '134'])).
% 4.52/4.72  thf('136', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 4.52/4.72      inference('demod', [status(thm)], ['38', '135'])).
% 4.52/4.72  thf('137', plain,
% 4.52/4.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 4.52/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.52/4.72  thf('138', plain, ($false),
% 4.52/4.72      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 4.52/4.72  
% 4.52/4.72  % SZS output end Refutation
% 4.52/4.72  
% 4.57/4.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
