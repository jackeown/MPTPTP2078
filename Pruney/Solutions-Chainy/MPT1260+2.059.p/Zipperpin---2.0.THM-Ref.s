%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s9gdHs1JYV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:32 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 327 expanded)
%              Number of leaves         :   41 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          : 1425 (3857 expanded)
%              Number of equality atoms :   97 ( 242 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ X47 @ X48 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','20'])).

thf('22',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v4_pre_topc @ X39 @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
        = X39 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k1_tops_1 @ X42 @ X41 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_pre_topc @ X42 @ ( k3_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 ) ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X28 @ ( k3_subset_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('48',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_tops_1 @ X46 @ X45 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ ( k2_pre_topc @ X46 @ X45 ) @ ( k1_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('60',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('62',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('63',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['64'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('86',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('93',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k1_tops_1 @ X50 @ X49 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 @ ( k2_tops_1 @ X50 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('102',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X43 @ X44 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('103',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','106'])).

thf('108',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s9gdHs1JYV
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.72/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.91  % Solved by: fo/fo7.sh
% 1.72/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.91  % done 1828 iterations in 1.449s
% 1.72/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.91  % SZS output start Refutation
% 1.72/1.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.72/1.91  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.72/1.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.72/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.91  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.72/1.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.72/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.72/1.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.72/1.91  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.72/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.91  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.72/1.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.72/1.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.91  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.72/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.91  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.72/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.91  thf(t76_tops_1, conjecture,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.91       ( ![B:$i]:
% 1.72/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91           ( ( v3_pre_topc @ B @ A ) <=>
% 1.72/1.91             ( ( k2_tops_1 @ A @ B ) =
% 1.72/1.91               ( k7_subset_1 @
% 1.72/1.91                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.72/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.91    (~( ![A:$i]:
% 1.72/1.91        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.91          ( ![B:$i]:
% 1.72/1.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91              ( ( v3_pre_topc @ B @ A ) <=>
% 1.72/1.91                ( ( k2_tops_1 @ A @ B ) =
% 1.72/1.91                  ( k7_subset_1 @
% 1.72/1.91                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.72/1.91    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.72/1.91  thf('0', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.72/1.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('1', plain,
% 1.72/1.91      (~
% 1.72/1.91       (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.72/1.91       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('split', [status(esa)], ['0'])).
% 1.72/1.91  thf('2', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.72/1.91        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('3', plain,
% 1.72/1.91      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('split', [status(esa)], ['2'])).
% 1.72/1.91  thf('4', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(t30_tops_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( l1_pre_topc @ A ) =>
% 1.72/1.91       ( ![B:$i]:
% 1.72/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91           ( ( v3_pre_topc @ B @ A ) <=>
% 1.72/1.91             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.72/1.91  thf('5', plain,
% 1.72/1.91      (![X47 : $i, X48 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.72/1.91          | ~ (v3_pre_topc @ X47 @ X48)
% 1.72/1.91          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47) @ X48)
% 1.72/1.91          | ~ (l1_pre_topc @ X48))),
% 1.72/1.91      inference('cnf', [status(esa)], [t30_tops_1])).
% 1.72/1.91  thf('6', plain,
% 1.72/1.91      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.91        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.72/1.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('sup-', [status(thm)], ['4', '5'])).
% 1.72/1.91  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('8', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(t3_subset, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.72/1.91  thf('9', plain,
% 1.72/1.91      (![X34 : $i, X35 : $i]:
% 1.72/1.91         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 1.72/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.72/1.91  thf('10', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.72/1.91      inference('sup-', [status(thm)], ['8', '9'])).
% 1.72/1.91  thf(t28_xboole_1, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.72/1.91  thf('11', plain,
% 1.72/1.91      (![X17 : $i, X18 : $i]:
% 1.72/1.91         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.72/1.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.72/1.91  thf('12', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.72/1.91      inference('sup-', [status(thm)], ['10', '11'])).
% 1.72/1.91  thf(commutativity_k3_xboole_0, axiom,
% 1.72/1.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.72/1.91  thf('13', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.72/1.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.72/1.91  thf(t100_xboole_1, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.72/1.91  thf('14', plain,
% 1.72/1.91      (![X15 : $i, X16 : $i]:
% 1.72/1.91         ((k4_xboole_0 @ X15 @ X16)
% 1.72/1.91           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.72/1.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.91  thf('15', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         ((k4_xboole_0 @ X0 @ X1)
% 1.72/1.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.72/1.91      inference('sup+', [status(thm)], ['13', '14'])).
% 1.72/1.91  thf('16', plain,
% 1.72/1.91      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['12', '15'])).
% 1.72/1.91  thf('17', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(d5_subset_1, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.91       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.72/1.91  thf('18', plain,
% 1.72/1.91      (![X23 : $i, X24 : $i]:
% 1.72/1.91         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 1.72/1.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 1.72/1.91      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.72/1.91  thf('19', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup-', [status(thm)], ['17', '18'])).
% 1.72/1.91  thf('20', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['16', '19'])).
% 1.72/1.91  thf('21', plain,
% 1.72/1.91      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.72/1.91        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['6', '7', '20'])).
% 1.72/1.91  thf('22', plain,
% 1.72/1.91      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.72/1.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['3', '21'])).
% 1.72/1.91  thf('23', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup-', [status(thm)], ['17', '18'])).
% 1.72/1.91  thf(t36_xboole_1, axiom,
% 1.72/1.91    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.72/1.91  thf('24', plain,
% 1.72/1.91      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.72/1.91      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.91  thf('25', plain,
% 1.72/1.91      (![X34 : $i, X36 : $i]:
% 1.72/1.91         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 1.72/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.72/1.91  thf('26', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.72/1.91      inference('sup-', [status(thm)], ['24', '25'])).
% 1.72/1.91  thf('27', plain,
% 1.72/1.91      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.72/1.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('sup+', [status(thm)], ['23', '26'])).
% 1.72/1.91  thf(t52_pre_topc, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( l1_pre_topc @ A ) =>
% 1.72/1.91       ( ![B:$i]:
% 1.72/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.72/1.91             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.72/1.91               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.72/1.91  thf('28', plain,
% 1.72/1.91      (![X39 : $i, X40 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.72/1.91          | ~ (v4_pre_topc @ X39 @ X40)
% 1.72/1.91          | ((k2_pre_topc @ X40 @ X39) = (X39))
% 1.72/1.91          | ~ (l1_pre_topc @ X40))),
% 1.72/1.91      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.72/1.91  thf('29', plain,
% 1.72/1.91      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.91        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.72/1.91      inference('sup-', [status(thm)], ['27', '28'])).
% 1.72/1.91  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('31', plain,
% 1.72/1.91      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['29', '30'])).
% 1.72/1.91  thf('32', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['16', '19'])).
% 1.72/1.91  thf('33', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['16', '19'])).
% 1.72/1.91  thf('34', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['16', '19'])).
% 1.72/1.91  thf('35', plain,
% 1.72/1.91      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.72/1.91      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.72/1.91  thf('36', plain,
% 1.72/1.91      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.72/1.91          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.72/1.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['22', '35'])).
% 1.72/1.91  thf('37', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(d1_tops_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( l1_pre_topc @ A ) =>
% 1.72/1.91       ( ![B:$i]:
% 1.72/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91           ( ( k1_tops_1 @ A @ B ) =
% 1.72/1.91             ( k3_subset_1 @
% 1.72/1.91               ( u1_struct_0 @ A ) @ 
% 1.72/1.91               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.72/1.91  thf('38', plain,
% 1.72/1.91      (![X41 : $i, X42 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.72/1.91          | ((k1_tops_1 @ X42 @ X41)
% 1.72/1.91              = (k3_subset_1 @ (u1_struct_0 @ X42) @ 
% 1.72/1.91                 (k2_pre_topc @ X42 @ (k3_subset_1 @ (u1_struct_0 @ X42) @ X41))))
% 1.72/1.91          | ~ (l1_pre_topc @ X42))),
% 1.72/1.91      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.72/1.91  thf('39', plain,
% 1.72/1.91      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.91        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.91            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91               (k2_pre_topc @ sk_A @ 
% 1.72/1.91                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['37', '38'])).
% 1.72/1.91  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('41', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['16', '19'])).
% 1.72/1.91  thf('42', plain,
% 1.72/1.91      (((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.91         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.72/1.91      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.72/1.91  thf('43', plain,
% 1.72/1.91      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.72/1.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('sup+', [status(thm)], ['36', '42'])).
% 1.72/1.91  thf('44', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(involutiveness_k3_subset_1, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.91       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.72/1.91  thf('45', plain,
% 1.72/1.91      (![X27 : $i, X28 : $i]:
% 1.72/1.91         (((k3_subset_1 @ X28 @ (k3_subset_1 @ X28 @ X27)) = (X27))
% 1.72/1.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 1.72/1.91      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.72/1.91  thf('46', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.72/1.91      inference('sup-', [status(thm)], ['44', '45'])).
% 1.72/1.91  thf('47', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.72/1.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.72/1.91      inference('sup+', [status(thm)], ['16', '19'])).
% 1.72/1.91  thf('48', plain,
% 1.72/1.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.72/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.72/1.91  thf('49', plain,
% 1.72/1.91      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.72/1.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('sup+', [status(thm)], ['43', '48'])).
% 1.72/1.91  thf('50', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(l78_tops_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( l1_pre_topc @ A ) =>
% 1.72/1.91       ( ![B:$i]:
% 1.72/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91           ( ( k2_tops_1 @ A @ B ) =
% 1.72/1.91             ( k7_subset_1 @
% 1.72/1.91               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.72/1.91               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.72/1.91  thf('51', plain,
% 1.72/1.91      (![X45 : $i, X46 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.72/1.91          | ((k2_tops_1 @ X46 @ X45)
% 1.72/1.91              = (k7_subset_1 @ (u1_struct_0 @ X46) @ 
% 1.72/1.91                 (k2_pre_topc @ X46 @ X45) @ (k1_tops_1 @ X46 @ X45)))
% 1.72/1.91          | ~ (l1_pre_topc @ X46))),
% 1.72/1.91      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.72/1.91  thf('52', plain,
% 1.72/1.91      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.91        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['50', '51'])).
% 1.72/1.91  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('54', plain,
% 1.72/1.91      (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.72/1.91            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.91      inference('demod', [status(thm)], ['52', '53'])).
% 1.72/1.91  thf('55', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.72/1.91         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('sup+', [status(thm)], ['49', '54'])).
% 1.72/1.91  thf('56', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.72/1.91         <= (~
% 1.72/1.91             (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('split', [status(esa)], ['0'])).
% 1.72/1.91  thf('57', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.91         <= (~
% 1.72/1.91             (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.72/1.91             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['55', '56'])).
% 1.72/1.91  thf('58', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.72/1.91       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('simplify', [status(thm)], ['57'])).
% 1.72/1.91  thf('59', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.72/1.91       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('split', [status(esa)], ['2'])).
% 1.72/1.91  thf(d4_xboole_0, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.72/1.91       ( ![D:$i]:
% 1.72/1.91         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.91           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.72/1.91  thf('60', plain,
% 1.72/1.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.72/1.91         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.72/1.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.72/1.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.72/1.91      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.91  thf(t3_boole, axiom,
% 1.72/1.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.72/1.91  thf('61', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.72/1.91      inference('cnf', [status(esa)], [t3_boole])).
% 1.72/1.91  thf(d5_xboole_0, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.72/1.91       ( ![D:$i]:
% 1.72/1.91         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.72/1.91  thf('62', plain,
% 1.72/1.91      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.72/1.91         (~ (r2_hidden @ X12 @ X11)
% 1.72/1.91          | ~ (r2_hidden @ X12 @ X10)
% 1.72/1.91          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 1.72/1.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.72/1.91  thf('63', plain,
% 1.72/1.91      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.72/1.91         (~ (r2_hidden @ X12 @ X10)
% 1.72/1.91          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.72/1.91      inference('simplify', [status(thm)], ['62'])).
% 1.72/1.91  thf('64', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.72/1.91      inference('sup-', [status(thm)], ['61', '63'])).
% 1.72/1.91  thf('65', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.72/1.91      inference('condensation', [status(thm)], ['64'])).
% 1.72/1.91  thf('66', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.72/1.91          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['60', '65'])).
% 1.72/1.91  thf('67', plain,
% 1.72/1.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.72/1.91         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.72/1.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.72/1.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.72/1.91      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.91  thf('68', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.72/1.91      inference('condensation', [status(thm)], ['64'])).
% 1.72/1.91  thf('69', plain,
% 1.72/1.91      (![X0 : $i, X1 : $i]:
% 1.72/1.91         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.72/1.91          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.72/1.91      inference('sup-', [status(thm)], ['67', '68'])).
% 1.72/1.91  thf('70', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(dt_k2_pre_topc, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( ( l1_pre_topc @ A ) & 
% 1.72/1.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.72/1.91       ( m1_subset_1 @
% 1.72/1.91         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.72/1.91  thf('71', plain,
% 1.72/1.91      (![X37 : $i, X38 : $i]:
% 1.72/1.91         (~ (l1_pre_topc @ X37)
% 1.72/1.91          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.72/1.91          | (m1_subset_1 @ (k2_pre_topc @ X37 @ X38) @ 
% 1.72/1.91             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 1.72/1.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.72/1.91  thf('72', plain,
% 1.72/1.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.72/1.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.72/1.91        | ~ (l1_pre_topc @ sk_A))),
% 1.72/1.91      inference('sup-', [status(thm)], ['70', '71'])).
% 1.72/1.91  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('74', plain,
% 1.72/1.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.72/1.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('demod', [status(thm)], ['72', '73'])).
% 1.72/1.91  thf(redefinition_k7_subset_1, axiom,
% 1.72/1.91    (![A:$i,B:$i,C:$i]:
% 1.72/1.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.91       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.72/1.91  thf('75', plain,
% 1.72/1.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.72/1.91          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 1.72/1.91      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.72/1.91  thf('76', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.72/1.91           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.72/1.91      inference('sup-', [status(thm)], ['74', '75'])).
% 1.72/1.91  thf('77', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('split', [status(esa)], ['2'])).
% 1.72/1.91  thf('78', plain,
% 1.72/1.91      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup+', [status(thm)], ['76', '77'])).
% 1.72/1.91  thf('79', plain,
% 1.72/1.91      (![X9 : $i, X10 : $i, X12 : $i]:
% 1.72/1.91         (~ (r2_hidden @ X12 @ X10)
% 1.72/1.91          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.72/1.91      inference('simplify', [status(thm)], ['62'])).
% 1.72/1.91  thf('80', plain,
% 1.72/1.91      ((![X0 : $i]:
% 1.72/1.91          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.91           | ~ (r2_hidden @ X0 @ sk_B)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['78', '79'])).
% 1.72/1.91  thf('81', plain,
% 1.72/1.91      ((![X0 : $i]:
% 1.72/1.91          (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.91           | ~ (r2_hidden @ 
% 1.72/1.91                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['69', '80'])).
% 1.72/1.91  thf('82', plain,
% 1.72/1.91      (((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.91         | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['66', '81'])).
% 1.72/1.91  thf('83', plain,
% 1.72/1.91      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('simplify', [status(thm)], ['82'])).
% 1.72/1.91  thf('84', plain,
% 1.72/1.91      (![X15 : $i, X16 : $i]:
% 1.72/1.91         ((k4_xboole_0 @ X15 @ X16)
% 1.72/1.91           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.72/1.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.91  thf('85', plain,
% 1.72/1.91      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.91          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup+', [status(thm)], ['83', '84'])).
% 1.72/1.91  thf(t2_boole, axiom,
% 1.72/1.91    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.72/1.91  thf('86', plain,
% 1.72/1.91      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 1.72/1.91      inference('cnf', [status(esa)], [t2_boole])).
% 1.72/1.91  thf('87', plain,
% 1.72/1.91      (![X15 : $i, X16 : $i]:
% 1.72/1.91         ((k4_xboole_0 @ X15 @ X16)
% 1.72/1.91           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.72/1.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.72/1.91  thf('88', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.72/1.91      inference('sup+', [status(thm)], ['86', '87'])).
% 1.72/1.91  thf('89', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.72/1.91      inference('cnf', [status(esa)], [t3_boole])).
% 1.72/1.91  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.72/1.91      inference('sup+', [status(thm)], ['88', '89'])).
% 1.72/1.91  thf('91', plain,
% 1.72/1.91      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('demod', [status(thm)], ['85', '90'])).
% 1.72/1.91  thf('92', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(t74_tops_1, axiom,
% 1.72/1.91    (![A:$i]:
% 1.72/1.91     ( ( l1_pre_topc @ A ) =>
% 1.72/1.91       ( ![B:$i]:
% 1.72/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.91           ( ( k1_tops_1 @ A @ B ) =
% 1.72/1.91             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.72/1.91  thf('93', plain,
% 1.72/1.91      (![X49 : $i, X50 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.72/1.91          | ((k1_tops_1 @ X50 @ X49)
% 1.72/1.91              = (k7_subset_1 @ (u1_struct_0 @ X50) @ X49 @ 
% 1.72/1.91                 (k2_tops_1 @ X50 @ X49)))
% 1.72/1.91          | ~ (l1_pre_topc @ X50))),
% 1.72/1.91      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.72/1.91  thf('94', plain,
% 1.72/1.91      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.91        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.91            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.91               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.72/1.91      inference('sup-', [status(thm)], ['92', '93'])).
% 1.72/1.91  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('96', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('97', plain,
% 1.72/1.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.72/1.91         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.72/1.91          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 1.72/1.91      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.72/1.91  thf('98', plain,
% 1.72/1.91      (![X0 : $i]:
% 1.72/1.91         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.72/1.91           = (k4_xboole_0 @ sk_B @ X0))),
% 1.72/1.91      inference('sup-', [status(thm)], ['96', '97'])).
% 1.72/1.91  thf('99', plain,
% 1.72/1.91      (((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.91         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.91      inference('demod', [status(thm)], ['94', '95', '98'])).
% 1.72/1.91  thf('100', plain,
% 1.72/1.91      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup+', [status(thm)], ['91', '99'])).
% 1.72/1.91  thf('101', plain,
% 1.72/1.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf(fc9_tops_1, axiom,
% 1.72/1.91    (![A:$i,B:$i]:
% 1.72/1.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.72/1.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.72/1.91       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.72/1.91  thf('102', plain,
% 1.72/1.91      (![X43 : $i, X44 : $i]:
% 1.72/1.91         (~ (l1_pre_topc @ X43)
% 1.72/1.91          | ~ (v2_pre_topc @ X43)
% 1.72/1.91          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.72/1.91          | (v3_pre_topc @ (k1_tops_1 @ X43 @ X44) @ X43))),
% 1.72/1.91      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.72/1.91  thf('103', plain,
% 1.72/1.91      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.72/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.72/1.91        | ~ (l1_pre_topc @ sk_A))),
% 1.72/1.91      inference('sup-', [status(thm)], ['101', '102'])).
% 1.72/1.91  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.91  thf('106', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.72/1.91      inference('demod', [status(thm)], ['103', '104', '105'])).
% 1.72/1.91  thf('107', plain,
% 1.72/1.91      (((v3_pre_topc @ sk_B @ sk_A))
% 1.72/1.91         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.72/1.91      inference('sup+', [status(thm)], ['100', '106'])).
% 1.72/1.91  thf('108', plain,
% 1.72/1.91      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.91      inference('split', [status(esa)], ['0'])).
% 1.72/1.91  thf('109', plain,
% 1.72/1.91      (~
% 1.72/1.91       (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.91             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.72/1.91       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.72/1.91      inference('sup-', [status(thm)], ['107', '108'])).
% 1.72/1.91  thf('110', plain, ($false),
% 1.72/1.91      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '109'])).
% 1.72/1.91  
% 1.72/1.91  % SZS output end Refutation
% 1.72/1.91  
% 1.72/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
