%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v12fYJIGmc

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:42 EST 2020

% Result     : Theorem 44.22s
% Output     : Refutation 44.22s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 515 expanded)
%              Number of leaves         :   45 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          : 2053 (5849 expanded)
%              Number of equality atoms :  155 ( 401 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X59 @ X58 ) @ X58 )
      | ~ ( v4_pre_topc @ X58 @ X59 )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k1_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) ) )
      = X24 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('66',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','67'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','70'])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','73'])).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('85',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('90',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('91',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('92',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k3_tarski @ ( k2_tarski @ X37 @ X39 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B @ X1 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( ( k4_subset_1 @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','93'])).

thf('95',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('99',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) ) )
      = X24 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('108',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('110',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('111',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('112',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) @ X23 ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','113'])).

thf('115',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) ) )
      = X24 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['102','118'])).

thf('120',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','119'])).

thf('121',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('122',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('124',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('125',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['123','128'])).

thf('130',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('131',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) ) )
      = X24 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('133',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('135',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('136',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) @ X23 ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) )
      = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) @ ( k3_tarski @ ( k2_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('144',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('145',plain,
    ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('147',plain,
    ( ( ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ sk_B )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('149',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('151',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['149','152'])).

thf('154',plain,
    ( ( sk_B
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['147','148','153'])).

thf('155',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','122','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('157',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k2_pre_topc @ X57 @ X56 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 @ ( k2_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['155','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('163',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X52 @ X53 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('164',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['161','167'])).

thf('169',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('170',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v12fYJIGmc
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 44.22/44.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.22/44.45  % Solved by: fo/fo7.sh
% 44.22/44.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.22/44.45  % done 30176 iterations in 43.996s
% 44.22/44.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.22/44.45  % SZS output start Refutation
% 44.22/44.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.22/44.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.22/44.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 44.22/44.45  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 44.22/44.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 44.22/44.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.22/44.45  thf(sk_B_type, type, sk_B: $i).
% 44.22/44.45  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 44.22/44.45  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 44.22/44.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.22/44.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 44.22/44.45  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 44.22/44.45  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 44.22/44.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 44.22/44.45  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 44.22/44.45  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 44.22/44.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 44.22/44.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.22/44.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 44.22/44.45  thf(sk_A_type, type, sk_A: $i).
% 44.22/44.45  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 44.22/44.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 44.22/44.45  thf(t77_tops_1, conjecture,
% 44.22/44.45    (![A:$i]:
% 44.22/44.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.22/44.45       ( ![B:$i]:
% 44.22/44.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.22/44.45           ( ( v4_pre_topc @ B @ A ) <=>
% 44.22/44.45             ( ( k2_tops_1 @ A @ B ) =
% 44.22/44.45               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 44.22/44.45  thf(zf_stmt_0, negated_conjecture,
% 44.22/44.45    (~( ![A:$i]:
% 44.22/44.45        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 44.22/44.45          ( ![B:$i]:
% 44.22/44.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.22/44.45              ( ( v4_pre_topc @ B @ A ) <=>
% 44.22/44.45                ( ( k2_tops_1 @ A @ B ) =
% 44.22/44.45                  ( k7_subset_1 @
% 44.22/44.45                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 44.22/44.45    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 44.22/44.45  thf('0', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45              (k1_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('1', plain,
% 44.22/44.45      (~
% 44.22/44.45       (((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 44.22/44.45       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 44.22/44.45      inference('split', [status(esa)], ['0'])).
% 44.22/44.45  thf('2', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45             (k1_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45        | (v4_pre_topc @ sk_B @ sk_A))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('3', plain,
% 44.22/44.45      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('split', [status(esa)], ['2'])).
% 44.22/44.45  thf('4', plain,
% 44.22/44.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf(t69_tops_1, axiom,
% 44.22/44.45    (![A:$i]:
% 44.22/44.45     ( ( l1_pre_topc @ A ) =>
% 44.22/44.45       ( ![B:$i]:
% 44.22/44.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.22/44.45           ( ( v4_pre_topc @ B @ A ) =>
% 44.22/44.45             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 44.22/44.45  thf('5', plain,
% 44.22/44.45      (![X58 : $i, X59 : $i]:
% 44.22/44.45         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 44.22/44.45          | (r1_tarski @ (k2_tops_1 @ X59 @ X58) @ X58)
% 44.22/44.45          | ~ (v4_pre_topc @ X58 @ X59)
% 44.22/44.45          | ~ (l1_pre_topc @ X59))),
% 44.22/44.45      inference('cnf', [status(esa)], [t69_tops_1])).
% 44.22/44.45  thf('6', plain,
% 44.22/44.45      ((~ (l1_pre_topc @ sk_A)
% 44.22/44.45        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 44.22/44.45        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 44.22/44.45      inference('sup-', [status(thm)], ['4', '5'])).
% 44.22/44.45  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('8', plain,
% 44.22/44.45      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 44.22/44.45        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 44.22/44.45      inference('demod', [status(thm)], ['6', '7'])).
% 44.22/44.45  thf('9', plain,
% 44.22/44.45      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['3', '8'])).
% 44.22/44.45  thf(t3_subset, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 44.22/44.45  thf('10', plain,
% 44.22/44.45      (![X47 : $i, X49 : $i]:
% 44.22/44.45         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 44.22/44.45      inference('cnf', [status(esa)], [t3_subset])).
% 44.22/44.45  thf('11', plain,
% 44.22/44.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['9', '10'])).
% 44.22/44.45  thf(involutiveness_k3_subset_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 44.22/44.45       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 44.22/44.45  thf('12', plain,
% 44.22/44.45      (![X35 : $i, X36 : $i]:
% 44.22/44.45         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 44.22/44.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 44.22/44.45      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 44.22/44.45  thf('13', plain,
% 44.22/44.45      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45          = (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['11', '12'])).
% 44.22/44.45  thf('14', plain,
% 44.22/44.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['9', '10'])).
% 44.22/44.45  thf(d5_subset_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 44.22/44.45       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 44.22/44.45  thf('15', plain,
% 44.22/44.45      (![X31 : $i, X32 : $i]:
% 44.22/44.45         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 44.22/44.45          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 44.22/44.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 44.22/44.45  thf('16', plain,
% 44.22/44.45      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 44.22/44.45          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['14', '15'])).
% 44.22/44.45  thf('17', plain,
% 44.22/44.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf(t74_tops_1, axiom,
% 44.22/44.45    (![A:$i]:
% 44.22/44.45     ( ( l1_pre_topc @ A ) =>
% 44.22/44.45       ( ![B:$i]:
% 44.22/44.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.22/44.45           ( ( k1_tops_1 @ A @ B ) =
% 44.22/44.45             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 44.22/44.45  thf('18', plain,
% 44.22/44.45      (![X60 : $i, X61 : $i]:
% 44.22/44.45         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 44.22/44.45          | ((k1_tops_1 @ X61 @ X60)
% 44.22/44.45              = (k7_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 44.22/44.45                 (k2_tops_1 @ X61 @ X60)))
% 44.22/44.45          | ~ (l1_pre_topc @ X61))),
% 44.22/44.45      inference('cnf', [status(esa)], [t74_tops_1])).
% 44.22/44.45  thf('19', plain,
% 44.22/44.45      ((~ (l1_pre_topc @ sk_A)
% 44.22/44.45        | ((k1_tops_1 @ sk_A @ sk_B)
% 44.22/44.45            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45               (k2_tops_1 @ sk_A @ sk_B))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['17', '18'])).
% 44.22/44.45  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('21', plain,
% 44.22/44.45      (((k1_tops_1 @ sk_A @ sk_B)
% 44.22/44.45         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 44.22/44.45      inference('demod', [status(thm)], ['19', '20'])).
% 44.22/44.45  thf('22', plain,
% 44.22/44.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf(redefinition_k7_subset_1, axiom,
% 44.22/44.45    (![A:$i,B:$i,C:$i]:
% 44.22/44.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 44.22/44.45       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 44.22/44.45  thf('23', plain,
% 44.22/44.45      (![X40 : $i, X41 : $i, X42 : $i]:
% 44.22/44.45         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 44.22/44.45          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 44.22/44.45      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 44.22/44.45  thf('24', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 44.22/44.45           = (k4_xboole_0 @ sk_B @ X0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['22', '23'])).
% 44.22/44.45  thf('25', plain,
% 44.22/44.45      (((k1_tops_1 @ sk_A @ sk_B)
% 44.22/44.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 44.22/44.45      inference('demod', [status(thm)], ['21', '24'])).
% 44.22/44.45  thf('26', plain,
% 44.22/44.45      ((((k1_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup+', [status(thm)], ['16', '25'])).
% 44.22/44.45  thf('27', plain,
% 44.22/44.45      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 44.22/44.45          = (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('demod', [status(thm)], ['13', '26'])).
% 44.22/44.45  thf('28', plain,
% 44.22/44.45      (((k1_tops_1 @ sk_A @ sk_B)
% 44.22/44.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 44.22/44.45      inference('demod', [status(thm)], ['21', '24'])).
% 44.22/44.45  thf(t36_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 44.22/44.45  thf('29', plain,
% 44.22/44.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 44.22/44.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 44.22/44.45  thf('30', plain,
% 44.22/44.45      (![X47 : $i, X49 : $i]:
% 44.22/44.45         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 44.22/44.45      inference('cnf', [status(esa)], [t3_subset])).
% 44.22/44.45  thf('31', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['29', '30'])).
% 44.22/44.45  thf('32', plain,
% 44.22/44.45      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 44.22/44.45      inference('sup+', [status(thm)], ['28', '31'])).
% 44.22/44.45  thf('33', plain,
% 44.22/44.45      (![X31 : $i, X32 : $i]:
% 44.22/44.45         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 44.22/44.45          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 44.22/44.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 44.22/44.45  thf('34', plain,
% 44.22/44.45      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 44.22/44.45         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['32', '33'])).
% 44.22/44.45  thf('35', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 44.22/44.45           = (k4_xboole_0 @ sk_B @ X0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['22', '23'])).
% 44.22/44.45  thf('36', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45              (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= (~
% 44.22/44.45             (((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('split', [status(esa)], ['0'])).
% 44.22/44.45  thf('37', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= (~
% 44.22/44.45             (((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['35', '36'])).
% 44.22/44.45  thf('38', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= (~
% 44.22/44.45             (((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['34', '37'])).
% 44.22/44.45  thf('39', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45         <= (~
% 44.22/44.45             (((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 44.22/44.45             ((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['27', '38'])).
% 44.22/44.45  thf('40', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 44.22/44.45       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 44.22/44.45      inference('simplify', [status(thm)], ['39'])).
% 44.22/44.45  thf('41', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 44.22/44.45       ((v4_pre_topc @ sk_B @ sk_A))),
% 44.22/44.45      inference('split', [status(esa)], ['2'])).
% 44.22/44.45  thf('42', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 44.22/44.45           = (k4_xboole_0 @ sk_B @ X0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['22', '23'])).
% 44.22/44.45  thf('43', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45             (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('split', [status(esa)], ['2'])).
% 44.22/44.45  thf('44', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['42', '43'])).
% 44.22/44.45  thf('45', plain,
% 44.22/44.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 44.22/44.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 44.22/44.45  thf(t43_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i,C:$i]:
% 44.22/44.45     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 44.22/44.45       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 44.22/44.45  thf('46', plain,
% 44.22/44.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 44.22/44.45         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 44.22/44.45          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 44.22/44.45      inference('cnf', [status(esa)], [t43_xboole_1])).
% 44.22/44.45  thf(l51_zfmisc_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 44.22/44.45  thf('47', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('48', plain,
% 44.22/44.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 44.22/44.45         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 44.22/44.45          | ~ (r1_tarski @ X15 @ (k3_tarski @ (k2_tarski @ X16 @ X17))))),
% 44.22/44.45      inference('demod', [status(thm)], ['46', '47'])).
% 44.22/44.45  thf('49', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.22/44.45         (r1_tarski @ 
% 44.22/44.45          (k4_xboole_0 @ 
% 44.22/44.45           (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 44.22/44.45          X0)),
% 44.22/44.45      inference('sup-', [status(thm)], ['45', '48'])).
% 44.22/44.45  thf(t1_boole, axiom,
% 44.22/44.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 44.22/44.45  thf('50', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 44.22/44.45      inference('cnf', [status(esa)], [t1_boole])).
% 44.22/44.45  thf('51', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('52', plain,
% 44.22/44.45      (![X5 : $i]: ((k3_tarski @ (k2_tarski @ X5 @ k1_xboole_0)) = (X5))),
% 44.22/44.45      inference('demod', [status(thm)], ['50', '51'])).
% 44.22/44.45  thf('53', plain,
% 44.22/44.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 44.22/44.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 44.22/44.45  thf(t44_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i,C:$i]:
% 44.22/44.45     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 44.22/44.45       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 44.22/44.45  thf('54', plain,
% 44.22/44.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 44.22/44.45         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 44.22/44.45          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 44.22/44.45      inference('cnf', [status(esa)], [t44_xboole_1])).
% 44.22/44.45  thf('55', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('56', plain,
% 44.22/44.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 44.22/44.45         ((r1_tarski @ X18 @ (k3_tarski @ (k2_tarski @ X19 @ X20)))
% 44.22/44.45          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 44.22/44.45      inference('demod', [status(thm)], ['54', '55'])).
% 44.22/44.45  thf('57', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['53', '56'])).
% 44.22/44.45  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 44.22/44.45      inference('sup+', [status(thm)], ['52', '57'])).
% 44.22/44.45  thf(t28_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 44.22/44.45  thf('59', plain,
% 44.22/44.45      (![X9 : $i, X10 : $i]:
% 44.22/44.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 44.22/44.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 44.22/44.45  thf('60', plain,
% 44.22/44.45      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['58', '59'])).
% 44.22/44.45  thf(t51_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 44.22/44.45       ( A ) ))).
% 44.22/44.45  thf('61', plain,
% 44.22/44.45      (![X24 : $i, X25 : $i]:
% 44.22/44.45         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 44.22/44.45           = (X24))),
% 44.22/44.45      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.22/44.45  thf('62', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('63', plain,
% 44.22/44.45      (![X24 : $i, X25 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25)))
% 44.22/44.45           = (X24))),
% 44.22/44.45      inference('demod', [status(thm)], ['61', '62'])).
% 44.22/44.45  thf('64', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))
% 44.22/44.45           = (k1_xboole_0))),
% 44.22/44.45      inference('sup+', [status(thm)], ['60', '63'])).
% 44.22/44.45  thf(commutativity_k2_tarski, axiom,
% 44.22/44.45    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 44.22/44.45  thf('65', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf('66', plain,
% 44.22/44.45      (![X5 : $i]: ((k3_tarski @ (k2_tarski @ X5 @ k1_xboole_0)) = (X5))),
% 44.22/44.45      inference('demod', [status(thm)], ['50', '51'])).
% 44.22/44.45  thf('67', plain,
% 44.22/44.45      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 44.22/44.45      inference('sup+', [status(thm)], ['65', '66'])).
% 44.22/44.45  thf('68', plain,
% 44.22/44.45      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.22/44.45      inference('demod', [status(thm)], ['64', '67'])).
% 44.22/44.45  thf(t38_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 44.22/44.45       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 44.22/44.45  thf('69', plain,
% 44.22/44.45      (![X13 : $i, X14 : $i]:
% 44.22/44.45         (((X13) = (k1_xboole_0))
% 44.22/44.45          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 44.22/44.45      inference('cnf', [status(esa)], [t38_xboole_1])).
% 44.22/44.45  thf('70', plain,
% 44.22/44.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['68', '69'])).
% 44.22/44.45  thf('71', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k4_xboole_0 @ 
% 44.22/44.45           (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1) @ 
% 44.22/44.45           X0) = (k1_xboole_0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['49', '70'])).
% 44.22/44.45  thf('72', plain,
% 44.22/44.45      (![X5 : $i]: ((k3_tarski @ (k2_tarski @ X5 @ k1_xboole_0)) = (X5))),
% 44.22/44.45      inference('demod', [status(thm)], ['50', '51'])).
% 44.22/44.45  thf('73', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 44.22/44.45      inference('demod', [status(thm)], ['71', '72'])).
% 44.22/44.45  thf('74', plain,
% 44.22/44.45      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['44', '73'])).
% 44.22/44.45  thf('75', plain,
% 44.22/44.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 44.22/44.45         ((r1_tarski @ X18 @ (k3_tarski @ (k2_tarski @ X19 @ X20)))
% 44.22/44.45          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 44.22/44.45      inference('demod', [status(thm)], ['54', '55'])).
% 44.22/44.45  thf('76', plain,
% 44.22/44.45      ((![X0 : $i]:
% 44.22/44.45          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 44.22/44.45           | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 44.22/44.45              (k3_tarski @ (k2_tarski @ sk_B @ X0)))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['74', '75'])).
% 44.22/44.45  thf('77', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 44.22/44.45      inference('sup+', [status(thm)], ['52', '57'])).
% 44.22/44.45  thf('78', plain,
% 44.22/44.45      ((![X0 : $i]:
% 44.22/44.45          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 44.22/44.45           (k3_tarski @ (k2_tarski @ sk_B @ X0))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['76', '77'])).
% 44.22/44.45  thf('79', plain,
% 44.22/44.45      (![X47 : $i, X49 : $i]:
% 44.22/44.45         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 44.22/44.45      inference('cnf', [status(esa)], [t3_subset])).
% 44.22/44.45  thf('80', plain,
% 44.22/44.45      ((![X0 : $i]:
% 44.22/44.45          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 44.22/44.45           (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ sk_B @ X0)))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['78', '79'])).
% 44.22/44.45  thf('81', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['53', '56'])).
% 44.22/44.45  thf('82', plain,
% 44.22/44.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('83', plain,
% 44.22/44.45      (![X47 : $i, X48 : $i]:
% 44.22/44.45         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 44.22/44.45      inference('cnf', [status(esa)], [t3_subset])).
% 44.22/44.45  thf('84', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 44.22/44.45      inference('sup-', [status(thm)], ['82', '83'])).
% 44.22/44.45  thf(t1_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i,C:$i]:
% 44.22/44.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 44.22/44.45       ( r1_tarski @ A @ C ) ))).
% 44.22/44.45  thf('85', plain,
% 44.22/44.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.22/44.45         (~ (r1_tarski @ X6 @ X7)
% 44.22/44.45          | ~ (r1_tarski @ X7 @ X8)
% 44.22/44.45          | (r1_tarski @ X6 @ X8))),
% 44.22/44.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 44.22/44.45  thf('86', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['84', '85'])).
% 44.22/44.45  thf('87', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         (r1_tarski @ sk_B @ 
% 44.22/44.45          (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['81', '86'])).
% 44.22/44.45  thf('88', plain,
% 44.22/44.45      (![X47 : $i, X49 : $i]:
% 44.22/44.45         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 44.22/44.45      inference('cnf', [status(esa)], [t3_subset])).
% 44.22/44.45  thf('89', plain,
% 44.22/44.45      (![X0 : $i]:
% 44.22/44.45         (m1_subset_1 @ sk_B @ 
% 44.22/44.45          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['87', '88'])).
% 44.22/44.45  thf(redefinition_k4_subset_1, axiom,
% 44.22/44.45    (![A:$i,B:$i,C:$i]:
% 44.22/44.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 44.22/44.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 44.22/44.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 44.22/44.45  thf('90', plain,
% 44.22/44.45      (![X37 : $i, X38 : $i, X39 : $i]:
% 44.22/44.45         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 44.22/44.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 44.22/44.45          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 44.22/44.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 44.22/44.45  thf('91', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('92', plain,
% 44.22/44.45      (![X37 : $i, X38 : $i, X39 : $i]:
% 44.22/44.45         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 44.22/44.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 44.22/44.45          | ((k4_subset_1 @ X38 @ X37 @ X39)
% 44.22/44.45              = (k3_tarski @ (k2_tarski @ X37 @ X39))))),
% 44.22/44.45      inference('demod', [status(thm)], ['90', '91'])).
% 44.22/44.45  thf('93', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (((k4_subset_1 @ 
% 44.22/44.45            (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))) @ sk_B @ X1)
% 44.22/44.45            = (k3_tarski @ (k2_tarski @ sk_B @ X1)))
% 44.22/44.45          | ~ (m1_subset_1 @ X1 @ 
% 44.22/44.45               (k1_zfmisc_1 @ 
% 44.22/44.45                (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['89', '92'])).
% 44.22/44.45  thf('94', plain,
% 44.22/44.45      ((((k4_subset_1 @ 
% 44.22/44.45          (k3_tarski @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_B @ 
% 44.22/44.45          (k2_tops_1 @ sk_A @ sk_B))
% 44.22/44.45          = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['80', '93'])).
% 44.22/44.45  thf('95', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 44.22/44.45      inference('sup-', [status(thm)], ['82', '83'])).
% 44.22/44.45  thf('96', plain,
% 44.22/44.45      (![X9 : $i, X10 : $i]:
% 44.22/44.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 44.22/44.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 44.22/44.45  thf('97', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 44.22/44.45      inference('sup-', [status(thm)], ['95', '96'])).
% 44.22/44.45  thf('98', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf(t12_setfam_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 44.22/44.45  thf('99', plain,
% 44.22/44.45      (![X45 : $i, X46 : $i]:
% 44.22/44.45         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 44.22/44.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 44.22/44.45  thf('100', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 44.22/44.45      inference('sup+', [status(thm)], ['98', '99'])).
% 44.22/44.45  thf('101', plain,
% 44.22/44.45      (![X45 : $i, X46 : $i]:
% 44.22/44.45         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 44.22/44.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 44.22/44.45  thf('102', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.22/44.45      inference('sup+', [status(thm)], ['100', '101'])).
% 44.22/44.45  thf('103', plain,
% 44.22/44.45      (![X24 : $i, X25 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25)))
% 44.22/44.45           = (X24))),
% 44.22/44.45      inference('demod', [status(thm)], ['61', '62'])).
% 44.22/44.45  thf(idempotence_k2_xboole_0, axiom,
% 44.22/44.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 44.22/44.45  thf('104', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 44.22/44.45      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 44.22/44.45  thf('105', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('106', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 44.22/44.45      inference('demod', [status(thm)], ['104', '105'])).
% 44.22/44.45  thf(t4_xboole_1, axiom,
% 44.22/44.45    (![A:$i,B:$i,C:$i]:
% 44.22/44.45     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 44.22/44.45       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 44.22/44.45  thf('107', plain,
% 44.22/44.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 44.22/44.45         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 44.22/44.45           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 44.22/44.45      inference('cnf', [status(esa)], [t4_xboole_1])).
% 44.22/44.45  thf('108', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('109', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('110', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('111', plain,
% 44.22/44.45      (![X28 : $i, X29 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 44.22/44.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.22/44.45  thf('112', plain,
% 44.22/44.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_tarski @ (k2_tarski @ X21 @ X22)) @ X23))
% 44.22/44.45           = (k3_tarski @ 
% 44.22/44.45              (k2_tarski @ X21 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 44.22/44.45  thf('113', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 44.22/44.45           = (k3_tarski @ 
% 44.22/44.45              (k2_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X0 @ X1)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['106', '112'])).
% 44.22/44.45  thf('114', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 44.22/44.45           = (k3_tarski @ (k2_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 44.22/44.45      inference('sup+', [status(thm)], ['103', '113'])).
% 44.22/44.45  thf('115', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf('116', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 44.22/44.45           = (k3_tarski @ (k2_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 44.22/44.45      inference('demod', [status(thm)], ['114', '115'])).
% 44.22/44.45  thf('117', plain,
% 44.22/44.45      (![X24 : $i, X25 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25)))
% 44.22/44.45           = (X24))),
% 44.22/44.45      inference('demod', [status(thm)], ['61', '62'])).
% 44.22/44.45  thf('118', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 44.22/44.45      inference('sup+', [status(thm)], ['116', '117'])).
% 44.22/44.45  thf('119', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_tarski @ (k2_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))) = (X0))),
% 44.22/44.45      inference('sup+', [status(thm)], ['102', '118'])).
% 44.22/44.45  thf('120', plain,
% 44.22/44.45      (((k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B))
% 44.22/44.45         = (u1_struct_0 @ sk_A))),
% 44.22/44.45      inference('sup+', [status(thm)], ['97', '119'])).
% 44.22/44.45  thf('121', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf('122', plain,
% 44.22/44.45      (((k3_tarski @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))
% 44.22/44.45         = (u1_struct_0 @ sk_A))),
% 44.22/44.45      inference('demod', [status(thm)], ['120', '121'])).
% 44.22/44.45  thf('123', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['42', '43'])).
% 44.22/44.45  thf('124', plain,
% 44.22/44.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 44.22/44.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 44.22/44.45  thf('125', plain,
% 44.22/44.45      (![X9 : $i, X10 : $i]:
% 44.22/44.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 44.22/44.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 44.22/44.45  thf('126', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 44.22/44.45           = (k4_xboole_0 @ X0 @ X1))),
% 44.22/44.45      inference('sup-', [status(thm)], ['124', '125'])).
% 44.22/44.45  thf('127', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.22/44.45      inference('sup+', [status(thm)], ['100', '101'])).
% 44.22/44.45  thf('128', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 44.22/44.45           = (k4_xboole_0 @ X0 @ X1))),
% 44.22/44.45      inference('demod', [status(thm)], ['126', '127'])).
% 44.22/44.45  thf('129', plain,
% 44.22/44.45      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 44.22/44.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['123', '128'])).
% 44.22/44.45  thf('130', plain,
% 44.22/44.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['42', '43'])).
% 44.22/44.45  thf('131', plain,
% 44.22/44.45      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 44.22/44.45          = (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['129', '130'])).
% 44.22/44.45  thf('132', plain,
% 44.22/44.45      (![X24 : $i, X25 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25)))
% 44.22/44.45           = (X24))),
% 44.22/44.45      inference('demod', [status(thm)], ['61', '62'])).
% 44.22/44.45  thf('133', plain,
% 44.22/44.45      ((((k3_tarski @ 
% 44.22/44.45          (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 44.22/44.45           (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 44.22/44.45          = (sk_B)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['131', '132'])).
% 44.22/44.45  thf('134', plain,
% 44.22/44.45      (((k1_tops_1 @ sk_A @ sk_B)
% 44.22/44.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 44.22/44.45      inference('demod', [status(thm)], ['21', '24'])).
% 44.22/44.45  thf('135', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf('136', plain,
% 44.22/44.45      ((((k3_tarski @ 
% 44.22/44.45          (k2_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45          = (sk_B)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['133', '134', '135'])).
% 44.22/44.45  thf('137', plain,
% 44.22/44.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ (k3_tarski @ (k2_tarski @ X21 @ X22)) @ X23))
% 44.22/44.45           = (k3_tarski @ 
% 44.22/44.45              (k2_tarski @ X21 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 44.22/44.45  thf('138', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 44.22/44.45      inference('demod', [status(thm)], ['104', '105'])).
% 44.22/44.45  thf('139', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_tarski @ 
% 44.22/44.45           (k2_tarski @ X1 @ 
% 44.22/44.45            (k3_tarski @ (k2_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))))
% 44.22/44.45           = (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 44.22/44.45      inference('sup+', [status(thm)], ['137', '138'])).
% 44.22/44.45  thf('140', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['53', '56'])).
% 44.22/44.45  thf('141', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (r1_tarski @ 
% 44.22/44.45          (k3_tarski @ (k2_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))) @ 
% 44.22/44.45          (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 44.22/44.45      inference('sup+', [status(thm)], ['139', '140'])).
% 44.22/44.45  thf('142', plain,
% 44.22/44.45      (((r1_tarski @ 
% 44.22/44.45         (k3_tarski @ (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)) @ 
% 44.22/44.45         (k3_tarski @ 
% 44.22/44.45          (k2_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['136', '141'])).
% 44.22/44.45  thf('143', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf('144', plain,
% 44.22/44.45      ((((k3_tarski @ 
% 44.22/44.45          (k2_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 44.22/44.45          = (sk_B)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['133', '134', '135'])).
% 44.22/44.45  thf('145', plain,
% 44.22/44.45      (((r1_tarski @ 
% 44.22/44.45         (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) @ sk_B))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['142', '143', '144'])).
% 44.22/44.45  thf('146', plain,
% 44.22/44.45      (![X9 : $i, X10 : $i]:
% 44.22/44.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 44.22/44.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 44.22/44.45  thf('147', plain,
% 44.22/44.45      ((((k3_xboole_0 @ 
% 44.22/44.45          (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) @ sk_B)
% 44.22/44.45          = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['145', '146'])).
% 44.22/44.45  thf('148', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.22/44.45      inference('sup+', [status(thm)], ['100', '101'])).
% 44.22/44.45  thf('149', plain,
% 44.22/44.45      (![X26 : $i, X27 : $i]:
% 44.22/44.45         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 44.22/44.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 44.22/44.45  thf('150', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 44.22/44.45      inference('sup-', [status(thm)], ['53', '56'])).
% 44.22/44.45  thf('151', plain,
% 44.22/44.45      (![X9 : $i, X10 : $i]:
% 44.22/44.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 44.22/44.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 44.22/44.45  thf('152', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_xboole_0 @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0))) = (X0))),
% 44.22/44.45      inference('sup-', [status(thm)], ['150', '151'])).
% 44.22/44.45  thf('153', plain,
% 44.22/44.45      (![X0 : $i, X1 : $i]:
% 44.22/44.45         ((k3_xboole_0 @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))) = (X1))),
% 44.22/44.45      inference('sup+', [status(thm)], ['149', '152'])).
% 44.22/44.45  thf('154', plain,
% 44.22/44.45      ((((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['147', '148', '153'])).
% 44.22/44.45  thf('155', plain,
% 44.22/44.45      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 44.22/44.45          = (sk_B)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('demod', [status(thm)], ['94', '122', '154'])).
% 44.22/44.45  thf('156', plain,
% 44.22/44.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf(t65_tops_1, axiom,
% 44.22/44.45    (![A:$i]:
% 44.22/44.45     ( ( l1_pre_topc @ A ) =>
% 44.22/44.45       ( ![B:$i]:
% 44.22/44.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.22/44.45           ( ( k2_pre_topc @ A @ B ) =
% 44.22/44.45             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 44.22/44.45  thf('157', plain,
% 44.22/44.45      (![X56 : $i, X57 : $i]:
% 44.22/44.45         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 44.22/44.45          | ((k2_pre_topc @ X57 @ X56)
% 44.22/44.45              = (k4_subset_1 @ (u1_struct_0 @ X57) @ X56 @ 
% 44.22/44.45                 (k2_tops_1 @ X57 @ X56)))
% 44.22/44.45          | ~ (l1_pre_topc @ X57))),
% 44.22/44.45      inference('cnf', [status(esa)], [t65_tops_1])).
% 44.22/44.45  thf('158', plain,
% 44.22/44.45      ((~ (l1_pre_topc @ sk_A)
% 44.22/44.45        | ((k2_pre_topc @ sk_A @ sk_B)
% 44.22/44.45            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45               (k2_tops_1 @ sk_A @ sk_B))))),
% 44.22/44.45      inference('sup-', [status(thm)], ['156', '157'])).
% 44.22/44.45  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('160', plain,
% 44.22/44.45      (((k2_pre_topc @ sk_A @ sk_B)
% 44.22/44.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 44.22/44.45      inference('demod', [status(thm)], ['158', '159'])).
% 44.22/44.45  thf('161', plain,
% 44.22/44.45      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['155', '160'])).
% 44.22/44.45  thf('162', plain,
% 44.22/44.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf(fc1_tops_1, axiom,
% 44.22/44.45    (![A:$i,B:$i]:
% 44.22/44.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 44.22/44.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 44.22/44.45       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 44.22/44.45  thf('163', plain,
% 44.22/44.45      (![X52 : $i, X53 : $i]:
% 44.22/44.45         (~ (l1_pre_topc @ X52)
% 44.22/44.45          | ~ (v2_pre_topc @ X52)
% 44.22/44.45          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 44.22/44.45          | (v4_pre_topc @ (k2_pre_topc @ X52 @ X53) @ X52))),
% 44.22/44.45      inference('cnf', [status(esa)], [fc1_tops_1])).
% 44.22/44.45  thf('164', plain,
% 44.22/44.45      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 44.22/44.45        | ~ (v2_pre_topc @ sk_A)
% 44.22/44.45        | ~ (l1_pre_topc @ sk_A))),
% 44.22/44.45      inference('sup-', [status(thm)], ['162', '163'])).
% 44.22/44.45  thf('165', plain, ((v2_pre_topc @ sk_A)),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 44.22/44.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.22/44.45  thf('167', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 44.22/44.45      inference('demod', [status(thm)], ['164', '165', '166'])).
% 44.22/44.45  thf('168', plain,
% 44.22/44.45      (((v4_pre_topc @ sk_B @ sk_A))
% 44.22/44.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 44.22/44.45      inference('sup+', [status(thm)], ['161', '167'])).
% 44.22/44.45  thf('169', plain,
% 44.22/44.45      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 44.22/44.45      inference('split', [status(esa)], ['0'])).
% 44.22/44.45  thf('170', plain,
% 44.22/44.45      (~
% 44.22/44.45       (((k2_tops_1 @ sk_A @ sk_B)
% 44.22/44.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 44.22/44.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 44.22/44.45       ((v4_pre_topc @ sk_B @ sk_A))),
% 44.22/44.45      inference('sup-', [status(thm)], ['168', '169'])).
% 44.22/44.45  thf('171', plain, ($false),
% 44.22/44.45      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '170'])).
% 44.22/44.45  
% 44.22/44.45  % SZS output end Refutation
% 44.22/44.45  
% 44.22/44.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
