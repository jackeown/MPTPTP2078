%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PvByTS05Aj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:23 EST 2020

% Result     : Theorem 22.85s
% Output     : Refutation 22.85s
% Verified   : 
% Statistics : Number of formulae       :  323 (2542 expanded)
%              Number of leaves         :   49 ( 817 expanded)
%              Depth                    :   20
%              Number of atoms          : 3017 (27755 expanded)
%              Number of equality atoms :  234 (1875 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( v3_pre_topc @ X63 @ X64 )
      | ~ ( r1_tarski @ X63 @ X65 )
      | ( r1_tarski @ X63 @ ( k1_tops_1 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X71 ) ) )
      | ( ( k1_tops_1 @ X71 @ X70 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X71 ) @ X70 @ ( k2_tops_1 @ X71 @ X70 ) ) )
      | ~ ( l1_pre_topc @ X71 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( ( k2_tops_1 @ X62 @ X61 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X62 ) @ ( k2_pre_topc @ X62 @ X61 ) @ ( k1_tops_1 @ X62 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('54',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('55',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('56',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['47','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('62',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('64',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('75',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('76',plain,(
    ! [X51: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('79',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('81',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('82',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( sk_B
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['72','83'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,
    ( sk_B
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['72','83'])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('92',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X57 @ X58 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('97',plain,(
    ! [X51: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('106',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ( ( k2_pre_topc @ X69 @ X68 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X69 ) @ X68 @ ( k2_tops_1 @ X69 @ X68 ) ) )
      | ~ ( l1_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['88','89'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','109','110','111'])).

thf('113',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','112'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X51: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('124',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('125',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('130',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('132',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['123','128','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('136',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('143',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('144',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('146',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['142','149'])).

thf('151',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['153','156','157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['134','159'])).

thf('161',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['113','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('163',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','112'])).

thf('164',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','112'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('166',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('167',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('170',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['168','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('176',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['174','177','178'])).

thf('180',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('186',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('189',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['184','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('194',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('195',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('201',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['199','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['193','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('210',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['193','207'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','190'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['212','213','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['184','191'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['179','192','217','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['165','219'])).

thf('221',plain,
    ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['164','220'])).

thf('222',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','112'])).

thf('223',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('224',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('225',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('226',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('228',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('230',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('233',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['230','233'])).

thf('235',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('236',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['223','238'])).

thf('240',plain,
    ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['221','222','239'])).

thf('241',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','240'])).

thf('242',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','109','110','111'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['165','219'])).

thf('244',plain,
    ( ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','109','110','111'])).

thf('246',plain,
    ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('248',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('249',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['246','249'])).

thf('251',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','109','110','111'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('253',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['253','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('259',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['251','252'])).

thf('260',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['257','258','259'])).

thf('261',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['250','260'])).

thf('262',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['241','261'])).

thf('263',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('264',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( l1_pre_topc @ X59 )
      | ~ ( v2_pre_topc @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X59 @ X60 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('265',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['262','268'])).

thf('270',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('271',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','60','61','271'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PvByTS05Aj
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 22.85/23.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 22.85/23.09  % Solved by: fo/fo7.sh
% 22.85/23.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.85/23.09  % done 40305 iterations in 22.631s
% 22.85/23.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 22.85/23.09  % SZS output start Refutation
% 22.85/23.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.85/23.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.85/23.09  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 22.85/23.09  thf(sk_A_type, type, sk_A: $i).
% 22.85/23.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 22.85/23.09  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 22.85/23.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.85/23.09  thf(sk_B_type, type, sk_B: $i).
% 22.85/23.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 22.85/23.09  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 22.85/23.09  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 22.85/23.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 22.85/23.09  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 22.85/23.09  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 22.85/23.09  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 22.85/23.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 22.85/23.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 22.85/23.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 22.85/23.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 22.85/23.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 22.85/23.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 22.85/23.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 22.85/23.09  thf(t76_tops_1, conjecture,
% 22.85/23.09    (![A:$i]:
% 22.85/23.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.85/23.09       ( ![B:$i]:
% 22.85/23.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09           ( ( v3_pre_topc @ B @ A ) <=>
% 22.85/23.09             ( ( k2_tops_1 @ A @ B ) =
% 22.85/23.09               ( k7_subset_1 @
% 22.85/23.09                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 22.85/23.09  thf(zf_stmt_0, negated_conjecture,
% 22.85/23.09    (~( ![A:$i]:
% 22.85/23.09        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 22.85/23.09          ( ![B:$i]:
% 22.85/23.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09              ( ( v3_pre_topc @ B @ A ) <=>
% 22.85/23.09                ( ( k2_tops_1 @ A @ B ) =
% 22.85/23.09                  ( k7_subset_1 @
% 22.85/23.09                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 22.85/23.09    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 22.85/23.09  thf('0', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 22.85/23.09        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('1', plain,
% 22.85/23.09      (~
% 22.85/23.09       (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 22.85/23.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('split', [status(esa)], ['0'])).
% 22.85/23.09  thf('2', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('3', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 22.85/23.09        | (v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('4', plain,
% 22.85/23.09      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('split', [status(esa)], ['3'])).
% 22.85/23.09  thf(t4_subset_1, axiom,
% 22.85/23.09    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 22.85/23.09  thf('5', plain,
% 22.85/23.09      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 22.85/23.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 22.85/23.09  thf('6', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(dt_k4_subset_1, axiom,
% 22.85/23.09    (![A:$i,B:$i,C:$i]:
% 22.85/23.09     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 22.85/23.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 22.85/23.09       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 22.85/23.09  thf('7', plain,
% 22.85/23.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 22.85/23.09          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 22.85/23.09          | (m1_subset_1 @ (k4_subset_1 @ X32 @ X31 @ X33) @ 
% 22.85/23.09             (k1_zfmisc_1 @ X32)))),
% 22.85/23.09      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 22.85/23.09  thf('8', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 22.85/23.09           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 22.85/23.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['6', '7'])).
% 22.85/23.09  thf('9', plain,
% 22.85/23.09      ((m1_subset_1 @ 
% 22.85/23.09        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['5', '8'])).
% 22.85/23.09  thf(t56_tops_1, axiom,
% 22.85/23.09    (![A:$i]:
% 22.85/23.09     ( ( l1_pre_topc @ A ) =>
% 22.85/23.09       ( ![B:$i]:
% 22.85/23.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09           ( ![C:$i]:
% 22.85/23.09             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 22.85/23.09                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 22.85/23.09  thf('10', plain,
% 22.85/23.09      (![X63 : $i, X64 : $i, X65 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 22.85/23.09          | ~ (v3_pre_topc @ X63 @ X64)
% 22.85/23.09          | ~ (r1_tarski @ X63 @ X65)
% 22.85/23.09          | (r1_tarski @ X63 @ (k1_tops_1 @ X64 @ X65))
% 22.85/23.09          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 22.85/23.09          | ~ (l1_pre_topc @ X64))),
% 22.85/23.09      inference('cnf', [status(esa)], [t56_tops_1])).
% 22.85/23.09  thf('11', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         (~ (l1_pre_topc @ sk_A)
% 22.85/23.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 22.85/23.09          | (r1_tarski @ 
% 22.85/23.09             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ 
% 22.85/23.09             (k1_tops_1 @ sk_A @ X0))
% 22.85/23.09          | ~ (r1_tarski @ 
% 22.85/23.09               (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ X0)
% 22.85/23.09          | ~ (v3_pre_topc @ 
% 22.85/23.09               (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ sk_A))),
% 22.85/23.09      inference('sup-', [status(thm)], ['9', '10'])).
% 22.85/23.09  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('13', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 22.85/23.09          | (r1_tarski @ 
% 22.85/23.09             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ 
% 22.85/23.09             (k1_tops_1 @ sk_A @ X0))
% 22.85/23.09          | ~ (r1_tarski @ 
% 22.85/23.09               (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ X0)
% 22.85/23.09          | ~ (v3_pre_topc @ 
% 22.85/23.09               (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ sk_A))),
% 22.85/23.09      inference('demod', [status(thm)], ['11', '12'])).
% 22.85/23.09  thf('14', plain,
% 22.85/23.09      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 22.85/23.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 22.85/23.09  thf('15', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(redefinition_k4_subset_1, axiom,
% 22.85/23.09    (![A:$i,B:$i,C:$i]:
% 22.85/23.09     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 22.85/23.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 22.85/23.09       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 22.85/23.09  thf('16', plain,
% 22.85/23.09      (![X39 : $i, X40 : $i, X41 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 22.85/23.09          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 22.85/23.09          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 22.85/23.09      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 22.85/23.09  thf('17', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 22.85/23.09            = (k2_xboole_0 @ sk_B @ X0))
% 22.85/23.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['15', '16'])).
% 22.85/23.09  thf('18', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0)
% 22.85/23.09         = (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['14', '17'])).
% 22.85/23.09  thf(commutativity_k2_xboole_0, axiom,
% 22.85/23.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 22.85/23.09  thf('19', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('20', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf(t1_boole, axiom,
% 22.85/23.09    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 22.85/23.09  thf('21', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 22.85/23.09      inference('cnf', [status(esa)], [t1_boole])).
% 22.85/23.09  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['20', '21'])).
% 22.85/23.09  thf('23', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['18', '19', '22'])).
% 22.85/23.09  thf('24', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['18', '19', '22'])).
% 22.85/23.09  thf('25', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['18', '19', '22'])).
% 22.85/23.09  thf('26', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 22.85/23.09          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 22.85/23.09          | ~ (r1_tarski @ sk_B @ X0)
% 22.85/23.09          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('demod', [status(thm)], ['13', '23', '24', '25'])).
% 22.85/23.09  thf('27', plain,
% 22.85/23.09      ((![X0 : $i]:
% 22.85/23.09          (~ (r1_tarski @ sk_B @ X0)
% 22.85/23.09           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 22.85/23.09           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 22.85/23.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['4', '26'])).
% 22.85/23.09  thf('28', plain,
% 22.85/23.09      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['2', '27'])).
% 22.85/23.09  thf(d10_xboole_0, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 22.85/23.09  thf('29', plain,
% 22.85/23.09      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 22.85/23.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.85/23.09  thf('30', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 22.85/23.09      inference('simplify', [status(thm)], ['29'])).
% 22.85/23.09  thf('31', plain,
% 22.85/23.09      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 22.85/23.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('demod', [status(thm)], ['28', '30'])).
% 22.85/23.09  thf('32', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(t74_tops_1, axiom,
% 22.85/23.09    (![A:$i]:
% 22.85/23.09     ( ( l1_pre_topc @ A ) =>
% 22.85/23.09       ( ![B:$i]:
% 22.85/23.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09           ( ( k1_tops_1 @ A @ B ) =
% 22.85/23.09             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 22.85/23.09  thf('33', plain,
% 22.85/23.09      (![X70 : $i, X71 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (u1_struct_0 @ X71)))
% 22.85/23.09          | ((k1_tops_1 @ X71 @ X70)
% 22.85/23.09              = (k7_subset_1 @ (u1_struct_0 @ X71) @ X70 @ 
% 22.85/23.09                 (k2_tops_1 @ X71 @ X70)))
% 22.85/23.09          | ~ (l1_pre_topc @ X71))),
% 22.85/23.09      inference('cnf', [status(esa)], [t74_tops_1])).
% 22.85/23.09  thf('34', plain,
% 22.85/23.09      ((~ (l1_pre_topc @ sk_A)
% 22.85/23.09        | ((k1_tops_1 @ sk_A @ sk_B)
% 22.85/23.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 22.85/23.09               (k2_tops_1 @ sk_A @ sk_B))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['32', '33'])).
% 22.85/23.09  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('36', plain,
% 22.85/23.09      (((k1_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 22.85/23.09            (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['34', '35'])).
% 22.85/23.09  thf('37', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(redefinition_k7_subset_1, axiom,
% 22.85/23.09    (![A:$i,B:$i,C:$i]:
% 22.85/23.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 22.85/23.09       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 22.85/23.09  thf('38', plain,
% 22.85/23.09      (![X42 : $i, X43 : $i, X44 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 22.85/23.09          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 22.85/23.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 22.85/23.09  thf('39', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 22.85/23.09           = (k4_xboole_0 @ sk_B @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['37', '38'])).
% 22.85/23.09  thf('40', plain,
% 22.85/23.09      (((k1_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['36', '39'])).
% 22.85/23.09  thf(t36_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 22.85/23.09  thf('41', plain,
% 22.85/23.09      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 22.85/23.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 22.85/23.09  thf('42', plain,
% 22.85/23.09      (![X2 : $i, X4 : $i]:
% 22.85/23.09         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 22.85/23.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 22.85/23.09  thf('43', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 22.85/23.09          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['41', '42'])).
% 22.85/23.09  thf('44', plain,
% 22.85/23.09      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 22.85/23.09        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['40', '43'])).
% 22.85/23.09  thf('45', plain,
% 22.85/23.09      (((k1_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['36', '39'])).
% 22.85/23.09  thf('46', plain,
% 22.85/23.09      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 22.85/23.09        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['44', '45'])).
% 22.85/23.09  thf('47', plain,
% 22.85/23.09      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 22.85/23.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['31', '46'])).
% 22.85/23.09  thf('48', plain,
% 22.85/23.09      ((m1_subset_1 @ 
% 22.85/23.09        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['5', '8'])).
% 22.85/23.09  thf(l78_tops_1, axiom,
% 22.85/23.09    (![A:$i]:
% 22.85/23.09     ( ( l1_pre_topc @ A ) =>
% 22.85/23.09       ( ![B:$i]:
% 22.85/23.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09           ( ( k2_tops_1 @ A @ B ) =
% 22.85/23.09             ( k7_subset_1 @
% 22.85/23.09               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 22.85/23.09               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 22.85/23.09  thf('49', plain,
% 22.85/23.09      (![X61 : $i, X62 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 22.85/23.09          | ((k2_tops_1 @ X62 @ X61)
% 22.85/23.09              = (k7_subset_1 @ (u1_struct_0 @ X62) @ 
% 22.85/23.09                 (k2_pre_topc @ X62 @ X61) @ (k1_tops_1 @ X62 @ X61)))
% 22.85/23.09          | ~ (l1_pre_topc @ X62))),
% 22.85/23.09      inference('cnf', [status(esa)], [l78_tops_1])).
% 22.85/23.09  thf('50', plain,
% 22.85/23.09      ((~ (l1_pre_topc @ sk_A)
% 22.85/23.09        | ((k2_tops_1 @ sk_A @ 
% 22.85/23.09            (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0))
% 22.85/23.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09               (k2_pre_topc @ sk_A @ 
% 22.85/23.09                (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0)) @ 
% 22.85/23.09               (k1_tops_1 @ sk_A @ 
% 22.85/23.09                (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0)))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['48', '49'])).
% 22.85/23.09  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('52', plain,
% 22.85/23.09      (((k2_tops_1 @ sk_A @ 
% 22.85/23.09         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0))
% 22.85/23.09         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09            (k2_pre_topc @ sk_A @ 
% 22.85/23.09             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0)) @ 
% 22.85/23.09            (k1_tops_1 @ sk_A @ 
% 22.85/23.09             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0))))),
% 22.85/23.09      inference('demod', [status(thm)], ['50', '51'])).
% 22.85/23.09  thf('53', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['18', '19', '22'])).
% 22.85/23.09  thf('54', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['18', '19', '22'])).
% 22.85/23.09  thf('55', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['18', '19', '22'])).
% 22.85/23.09  thf('56', plain,
% 22.85/23.09      (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 22.85/23.09  thf('57', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 22.85/23.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['47', '56'])).
% 22.85/23.09  thf('58', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 22.85/23.09         <= (~
% 22.85/23.09             (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('split', [status(esa)], ['0'])).
% 22.85/23.09  thf('59', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 22.85/23.09         <= (~
% 22.85/23.09             (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 22.85/23.09             ((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['57', '58'])).
% 22.85/23.09  thf('60', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 22.85/23.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('simplify', [status(thm)], ['59'])).
% 22.85/23.09  thf('61', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 22.85/23.09       ((v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('split', [status(esa)], ['3'])).
% 22.85/23.09  thf('62', plain,
% 22.85/23.09      (((k1_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['36', '39'])).
% 22.85/23.09  thf(t39_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 22.85/23.09  thf('63', plain,
% 22.85/23.09      (![X18 : $i, X19 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 22.85/23.09           = (k2_xboole_0 @ X18 @ X19))),
% 22.85/23.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 22.85/23.09  thf('64', plain,
% 22.85/23.09      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['62', '63'])).
% 22.85/23.09  thf('65', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('66', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('67', plain,
% 22.85/23.09      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['64', '65', '66'])).
% 22.85/23.09  thf('68', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(d5_subset_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 22.85/23.09       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 22.85/23.09  thf('69', plain,
% 22.85/23.09      (![X27 : $i, X28 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 22.85/23.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 22.85/23.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 22.85/23.09  thf('70', plain,
% 22.85/23.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 22.85/23.09      inference('sup-', [status(thm)], ['68', '69'])).
% 22.85/23.09  thf(t48_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 22.85/23.09  thf('71', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('72', plain,
% 22.85/23.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 22.85/23.09         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['70', '71'])).
% 22.85/23.09  thf('73', plain,
% 22.85/23.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 22.85/23.09      inference('sup-', [status(thm)], ['68', '69'])).
% 22.85/23.09  thf('74', plain,
% 22.85/23.09      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 22.85/23.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 22.85/23.09  thf('75', plain,
% 22.85/23.09      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 22.85/23.09        (u1_struct_0 @ sk_A))),
% 22.85/23.09      inference('sup+', [status(thm)], ['73', '74'])).
% 22.85/23.09  thf(t3_subset, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.85/23.09  thf('76', plain,
% 22.85/23.09      (![X51 : $i, X53 : $i]:
% 22.85/23.09         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X51 @ X53))),
% 22.85/23.09      inference('cnf', [status(esa)], [t3_subset])).
% 22.85/23.09  thf('77', plain,
% 22.85/23.09      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['75', '76'])).
% 22.85/23.09  thf('78', plain,
% 22.85/23.09      (![X27 : $i, X28 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 22.85/23.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 22.85/23.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 22.85/23.09  thf('79', plain,
% 22.85/23.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 22.85/23.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['77', '78'])).
% 22.85/23.09  thf('80', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(involutiveness_k3_subset_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 22.85/23.09       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 22.85/23.09  thf('81', plain,
% 22.85/23.09      (![X37 : $i, X38 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 22.85/23.09          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 22.85/23.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 22.85/23.09  thf('82', plain,
% 22.85/23.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 22.85/23.09      inference('sup-', [status(thm)], ['80', '81'])).
% 22.85/23.09  thf('83', plain,
% 22.85/23.09      (((sk_B)
% 22.85/23.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['79', '82'])).
% 22.85/23.09  thf('84', plain, (((sk_B) = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['72', '83'])).
% 22.85/23.09  thf(t100_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 22.85/23.09  thf('85', plain,
% 22.85/23.09      (![X8 : $i, X9 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X8 @ X9)
% 22.85/23.09           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 22.85/23.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.85/23.09  thf('86', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('87', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['85', '86'])).
% 22.85/23.09  thf('88', plain,
% 22.85/23.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 22.85/23.09         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['84', '87'])).
% 22.85/23.09  thf('89', plain, (((sk_B) = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['72', '83'])).
% 22.85/23.09  thf('90', plain,
% 22.85/23.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['88', '89'])).
% 22.85/23.09  thf('91', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(dt_k2_tops_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( ( l1_pre_topc @ A ) & 
% 22.85/23.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 22.85/23.09       ( m1_subset_1 @
% 22.85/23.09         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 22.85/23.09  thf('92', plain,
% 22.85/23.09      (![X57 : $i, X58 : $i]:
% 22.85/23.09         (~ (l1_pre_topc @ X57)
% 22.85/23.09          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 22.85/23.09          | (m1_subset_1 @ (k2_tops_1 @ X57 @ X58) @ 
% 22.85/23.09             (k1_zfmisc_1 @ (u1_struct_0 @ X57))))),
% 22.85/23.09      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 22.85/23.09  thf('93', plain,
% 22.85/23.09      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 22.85/23.09         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 22.85/23.09        | ~ (l1_pre_topc @ sk_A))),
% 22.85/23.09      inference('sup-', [status(thm)], ['91', '92'])).
% 22.85/23.09  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('95', plain,
% 22.85/23.09      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('demod', [status(thm)], ['93', '94'])).
% 22.85/23.09  thf('96', plain,
% 22.85/23.09      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 22.85/23.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 22.85/23.09  thf('97', plain,
% 22.85/23.09      (![X51 : $i, X53 : $i]:
% 22.85/23.09         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X51 @ X53))),
% 22.85/23.09      inference('cnf', [status(esa)], [t3_subset])).
% 22.85/23.09  thf('98', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['96', '97'])).
% 22.85/23.09  thf('99', plain,
% 22.85/23.09      (![X39 : $i, X40 : $i, X41 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 22.85/23.09          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 22.85/23.09          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 22.85/23.09      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 22.85/23.09  thf('100', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.85/23.09         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 22.85/23.09            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 22.85/23.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['98', '99'])).
% 22.85/23.09  thf('101', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 22.85/23.09           (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 22.85/23.09              (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['95', '100'])).
% 22.85/23.09  thf('102', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('103', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 22.85/23.09           (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 22.85/23.09              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['101', '102'])).
% 22.85/23.09  thf('104', plain,
% 22.85/23.09      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 22.85/23.09            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 22.85/23.09      inference('sup+', [status(thm)], ['90', '103'])).
% 22.85/23.09  thf('105', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(t65_tops_1, axiom,
% 22.85/23.09    (![A:$i]:
% 22.85/23.09     ( ( l1_pre_topc @ A ) =>
% 22.85/23.09       ( ![B:$i]:
% 22.85/23.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 22.85/23.09           ( ( k2_pre_topc @ A @ B ) =
% 22.85/23.09             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 22.85/23.09  thf('106', plain,
% 22.85/23.09      (![X68 : $i, X69 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 22.85/23.09          | ((k2_pre_topc @ X69 @ X68)
% 22.85/23.09              = (k4_subset_1 @ (u1_struct_0 @ X69) @ X68 @ 
% 22.85/23.09                 (k2_tops_1 @ X69 @ X68)))
% 22.85/23.09          | ~ (l1_pre_topc @ X69))),
% 22.85/23.09      inference('cnf', [status(esa)], [t65_tops_1])).
% 22.85/23.09  thf('107', plain,
% 22.85/23.09      ((~ (l1_pre_topc @ sk_A)
% 22.85/23.09        | ((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 22.85/23.09               (k2_tops_1 @ sk_A @ sk_B))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['105', '106'])).
% 22.85/23.09  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('109', plain,
% 22.85/23.09      (((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 22.85/23.09            (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['107', '108'])).
% 22.85/23.09  thf('110', plain,
% 22.85/23.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['88', '89'])).
% 22.85/23.09  thf('111', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('112', plain,
% 22.85/23.09      (((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['104', '109', '110', '111'])).
% 22.85/23.09  thf('113', plain,
% 22.85/23.09      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_pre_topc @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['67', '112'])).
% 22.85/23.09  thf(t46_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 22.85/23.09  thf('114', plain,
% 22.85/23.09      (![X21 : $i, X22 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 22.85/23.09      inference('cnf', [status(esa)], [t46_xboole_1])).
% 22.85/23.09  thf(l32_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.85/23.09  thf('115', plain,
% 22.85/23.09      (![X5 : $i, X6 : $i]:
% 22.85/23.09         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 22.85/23.09      inference('cnf', [status(esa)], [l32_xboole_1])).
% 22.85/23.09  thf('116', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (((k1_xboole_0) != (k1_xboole_0))
% 22.85/23.09          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['114', '115'])).
% 22.85/23.09  thf('117', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('simplify', [status(thm)], ['116'])).
% 22.85/23.09  thf('118', plain,
% 22.85/23.09      (![X51 : $i, X53 : $i]:
% 22.85/23.09         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X51 @ X53))),
% 22.85/23.09      inference('cnf', [status(esa)], [t3_subset])).
% 22.85/23.09  thf('119', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['117', '118'])).
% 22.85/23.09  thf('120', plain,
% 22.85/23.09      (![X27 : $i, X28 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 22.85/23.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 22.85/23.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 22.85/23.09  thf('121', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 22.85/23.09           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 22.85/23.09      inference('sup-', [status(thm)], ['119', '120'])).
% 22.85/23.09  thf('122', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('123', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 22.85/23.09           (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 22.85/23.09           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['121', '122'])).
% 22.85/23.09  thf(commutativity_k2_tarski, axiom,
% 22.85/23.09    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 22.85/23.09  thf('124', plain,
% 22.85/23.09      (![X25 : $i, X26 : $i]:
% 22.85/23.09         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 22.85/23.09  thf(t12_setfam_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 22.85/23.09  thf('125', plain,
% 22.85/23.09      (![X49 : $i, X50 : $i]:
% 22.85/23.09         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 22.85/23.09      inference('cnf', [status(esa)], [t12_setfam_1])).
% 22.85/23.09  thf('126', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['124', '125'])).
% 22.85/23.09  thf('127', plain,
% 22.85/23.09      (![X49 : $i, X50 : $i]:
% 22.85/23.09         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 22.85/23.09      inference('cnf', [status(esa)], [t12_setfam_1])).
% 22.85/23.09  thf('128', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('129', plain,
% 22.85/23.09      (![X21 : $i, X22 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 22.85/23.09      inference('cnf', [status(esa)], [t46_xboole_1])).
% 22.85/23.09  thf('130', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('131', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 22.85/23.09           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['129', '130'])).
% 22.85/23.09  thf(t3_boole, axiom,
% 22.85/23.09    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 22.85/23.09  thf('132', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 22.85/23.09      inference('cnf', [status(esa)], [t3_boole])).
% 22.85/23.09  thf('133', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['131', '132'])).
% 22.85/23.09  thf('134', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 22.85/23.09           (k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)) = (X0))),
% 22.85/23.09      inference('demod', [status(thm)], ['123', '128', '133'])).
% 22.85/23.09  thf('135', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('136', plain,
% 22.85/23.09      (![X21 : $i, X22 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 22.85/23.09      inference('cnf', [status(esa)], [t46_xboole_1])).
% 22.85/23.09  thf('137', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['135', '136'])).
% 22.85/23.09  thf('138', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('139', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 22.85/23.09           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['137', '138'])).
% 22.85/23.09  thf('140', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 22.85/23.09      inference('cnf', [status(esa)], [t3_boole])).
% 22.85/23.09  thf('141', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['139', '140'])).
% 22.85/23.09  thf('142', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('143', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('144', plain,
% 22.85/23.09      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 22.85/23.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 22.85/23.09  thf('145', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 22.85/23.09      inference('sup+', [status(thm)], ['143', '144'])).
% 22.85/23.09  thf(t28_xboole_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 22.85/23.09  thf('146', plain,
% 22.85/23.09      (![X14 : $i, X15 : $i]:
% 22.85/23.09         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 22.85/23.09      inference('cnf', [status(esa)], [t28_xboole_1])).
% 22.85/23.09  thf('147', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 22.85/23.09           = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup-', [status(thm)], ['145', '146'])).
% 22.85/23.09  thf('148', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('149', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('demod', [status(thm)], ['147', '148'])).
% 22.85/23.09  thf('150', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['142', '149'])).
% 22.85/23.09  thf('151', plain,
% 22.85/23.09      (![X8 : $i, X9 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X8 @ X9)
% 22.85/23.09           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 22.85/23.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.85/23.09  thf('152', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['150', '151'])).
% 22.85/23.09  thf('153', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 22.85/23.09           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 22.85/23.09              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['141', '152'])).
% 22.85/23.09  thf('154', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('155', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 22.85/23.09           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 22.85/23.09      inference('sup-', [status(thm)], ['119', '120'])).
% 22.85/23.09  thf('156', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 22.85/23.09           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['154', '155'])).
% 22.85/23.09  thf('157', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('158', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['139', '140'])).
% 22.85/23.09  thf('159', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 22.85/23.09           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 22.85/23.09      inference('demod', [status(thm)], ['153', '156', '157', '158'])).
% 22.85/23.09  thf('160', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 22.85/23.09           (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 22.85/23.09      inference('demod', [status(thm)], ['134', '159'])).
% 22.85/23.09  thf('161', plain,
% 22.85/23.09      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09         (k5_xboole_0 @ 
% 22.85/23.09          (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 22.85/23.09          (k1_tops_1 @ sk_A @ sk_B)))
% 22.85/23.09         = (k1_tops_1 @ sk_A @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['113', '160'])).
% 22.85/23.09  thf('162', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('163', plain,
% 22.85/23.09      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_pre_topc @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['67', '112'])).
% 22.85/23.09  thf('164', plain,
% 22.85/23.09      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_pre_topc @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['67', '112'])).
% 22.85/23.09  thf('165', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['131', '132'])).
% 22.85/23.09  thf('166', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('167', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('168', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['166', '167'])).
% 22.85/23.09  thf('169', plain,
% 22.85/23.09      (![X8 : $i, X9 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X8 @ X9)
% 22.85/23.09           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 22.85/23.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.85/23.09  thf('170', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('171', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['169', '170'])).
% 22.85/23.09  thf('172', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['166', '167'])).
% 22.85/23.09  thf('173', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('demod', [status(thm)], ['171', '172'])).
% 22.85/23.09  thf('174', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ X1 @ 
% 22.85/23.09           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['168', '173'])).
% 22.85/23.09  thf('175', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['96', '97'])).
% 22.85/23.09  thf('176', plain,
% 22.85/23.09      (![X27 : $i, X28 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 22.85/23.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 22.85/23.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 22.85/23.09  thf('177', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['175', '176'])).
% 22.85/23.09  thf('178', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['166', '167'])).
% 22.85/23.09  thf('179', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ X1 @ 
% 22.85/23.09           (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))
% 22.85/23.09           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['174', '177', '178'])).
% 22.85/23.09  thf('180', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('181', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['96', '97'])).
% 22.85/23.09  thf('182', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['180', '181'])).
% 22.85/23.09  thf('183', plain,
% 22.85/23.09      (![X27 : $i, X28 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 22.85/23.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 22.85/23.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 22.85/23.09  thf('184', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['182', '183'])).
% 22.85/23.09  thf('185', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['96', '97'])).
% 22.85/23.09  thf('186', plain,
% 22.85/23.09      (![X37 : $i, X38 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 22.85/23.09          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 22.85/23.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 22.85/23.09  thf('187', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup-', [status(thm)], ['185', '186'])).
% 22.85/23.09  thf('188', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['175', '176'])).
% 22.85/23.09  thf('189', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('190', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['188', '189'])).
% 22.85/23.09  thf('191', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('demod', [status(thm)], ['187', '190'])).
% 22.85/23.09  thf('192', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X0 @ X1)
% 22.85/23.09           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 22.85/23.09      inference('demod', [status(thm)], ['184', '191'])).
% 22.85/23.09  thf('193', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('194', plain,
% 22.85/23.09      (![X23 : $i, X24 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 22.85/23.09           = (k3_xboole_0 @ X23 @ X24))),
% 22.85/23.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.85/23.09  thf('195', plain,
% 22.85/23.09      (![X18 : $i, X19 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 22.85/23.09           = (k2_xboole_0 @ X18 @ X19))),
% 22.85/23.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 22.85/23.09  thf('196', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['194', '195'])).
% 22.85/23.09  thf('197', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('198', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.85/23.09  thf('199', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['196', '197', '198'])).
% 22.85/23.09  thf('200', plain,
% 22.85/23.09      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 22.85/23.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 22.85/23.09  thf('201', plain,
% 22.85/23.09      (![X5 : $i, X7 : $i]:
% 22.85/23.09         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 22.85/23.09      inference('cnf', [status(esa)], [l32_xboole_1])).
% 22.85/23.09  thf('202', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['200', '201'])).
% 22.85/23.09  thf('203', plain,
% 22.85/23.09      (![X18 : $i, X19 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 22.85/23.09           = (k2_xboole_0 @ X18 @ X19))),
% 22.85/23.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 22.85/23.09  thf('204', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 22.85/23.09           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['202', '203'])).
% 22.85/23.09  thf('205', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 22.85/23.09      inference('cnf', [status(esa)], [t1_boole])).
% 22.85/23.09  thf('206', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['204', '205'])).
% 22.85/23.09  thf('207', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (X1))),
% 22.85/23.09      inference('demod', [status(thm)], ['199', '206'])).
% 22.85/23.09  thf('208', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['193', '207'])).
% 22.85/23.09  thf('209', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['117', '118'])).
% 22.85/23.09  thf('210', plain,
% 22.85/23.09      (![X37 : $i, X38 : $i]:
% 22.85/23.09         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 22.85/23.09          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 22.85/23.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 22.85/23.09  thf('211', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 22.85/23.09           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 22.85/23.09      inference('sup-', [status(thm)], ['209', '210'])).
% 22.85/23.09  thf('212', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ 
% 22.85/23.09           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 22.85/23.09           (k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['208', '211'])).
% 22.85/23.09  thf('213', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['193', '207'])).
% 22.85/23.09  thf('214', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('215', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('demod', [status(thm)], ['187', '190'])).
% 22.85/23.09  thf('216', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 22.85/23.09           = (k4_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['214', '215'])).
% 22.85/23.09  thf('217', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('demod', [status(thm)], ['212', '213', '216'])).
% 22.85/23.09  thf('218', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X0 @ X1)
% 22.85/23.09           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 22.85/23.09      inference('demod', [status(thm)], ['184', '191'])).
% 22.85/23.09  thf('219', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 22.85/23.09           = (k4_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('demod', [status(thm)], ['179', '192', '217', '218'])).
% 22.85/23.09  thf('220', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 22.85/23.09           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['165', '219'])).
% 22.85/23.09  thf('221', plain,
% 22.85/23.09      (((k5_xboole_0 @ 
% 22.85/23.09         (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 22.85/23.09         (k1_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['164', '220'])).
% 22.85/23.09  thf('222', plain,
% 22.85/23.09      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_pre_topc @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['67', '112'])).
% 22.85/23.09  thf('223', plain,
% 22.85/23.09      (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 22.85/23.09  thf('224', plain,
% 22.85/23.09      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('demod', [status(thm)], ['93', '94'])).
% 22.85/23.09  thf('225', plain,
% 22.85/23.09      (![X51 : $i, X52 : $i]:
% 22.85/23.09         ((r1_tarski @ X51 @ X52) | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 22.85/23.09      inference('cnf', [status(esa)], [t3_subset])).
% 22.85/23.09  thf('226', plain,
% 22.85/23.09      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 22.85/23.09      inference('sup-', [status(thm)], ['224', '225'])).
% 22.85/23.09  thf('227', plain,
% 22.85/23.09      (![X14 : $i, X15 : $i]:
% 22.85/23.09         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 22.85/23.09      inference('cnf', [status(esa)], [t28_xboole_1])).
% 22.85/23.09  thf('228', plain,
% 22.85/23.09      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 22.85/23.09         = (k2_tops_1 @ sk_A @ sk_B))),
% 22.85/23.09      inference('sup-', [status(thm)], ['226', '227'])).
% 22.85/23.09  thf('229', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('230', plain,
% 22.85/23.09      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_tops_1 @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['228', '229'])).
% 22.85/23.09  thf('231', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['180', '181'])).
% 22.85/23.09  thf('232', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 22.85/23.09           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 22.85/23.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 22.85/23.09      inference('sup-', [status(thm)], ['6', '7'])).
% 22.85/23.09  thf('233', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         (m1_subset_1 @ 
% 22.85/23.09          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 22.85/23.09           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 22.85/23.09          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('sup-', [status(thm)], ['231', '232'])).
% 22.85/23.09  thf('234', plain,
% 22.85/23.09      ((m1_subset_1 @ 
% 22.85/23.09        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['230', '233'])).
% 22.85/23.09  thf('235', plain,
% 22.85/23.09      (((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 22.85/23.09            (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['107', '108'])).
% 22.85/23.09  thf('236', plain,
% 22.85/23.09      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('demod', [status(thm)], ['234', '235'])).
% 22.85/23.09  thf('237', plain,
% 22.85/23.09      (![X42 : $i, X43 : $i, X44 : $i]:
% 22.85/23.09         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 22.85/23.09          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 22.85/23.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 22.85/23.09  thf('238', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['236', '237'])).
% 22.85/23.09  thf('239', plain,
% 22.85/23.09      (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['223', '238'])).
% 22.85/23.09  thf('240', plain,
% 22.85/23.09      (((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k2_tops_1 @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['221', '222', '239'])).
% 22.85/23.09  thf('241', plain,
% 22.85/23.09      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09         = (k1_tops_1 @ sk_A @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['161', '162', '163', '240'])).
% 22.85/23.09  thf('242', plain,
% 22.85/23.09      (((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['104', '109', '110', '111'])).
% 22.85/23.09  thf('243', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 22.85/23.09           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['165', '219'])).
% 22.85/23.09  thf('244', plain,
% 22.85/23.09      (((k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['242', '243'])).
% 22.85/23.09  thf('245', plain,
% 22.85/23.09      (((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['104', '109', '110', '111'])).
% 22.85/23.09  thf('246', plain,
% 22.85/23.09      (((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 22.85/23.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['244', '245'])).
% 22.85/23.09  thf('247', plain,
% 22.85/23.09      (![X0 : $i]:
% 22.85/23.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 22.85/23.09      inference('sup-', [status(thm)], ['236', '237'])).
% 22.85/23.09  thf('248', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 22.85/23.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('split', [status(esa)], ['3'])).
% 22.85/23.09  thf('249', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 22.85/23.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('sup+', [status(thm)], ['247', '248'])).
% 22.85/23.09  thf('250', plain,
% 22.85/23.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 22.85/23.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('sup+', [status(thm)], ['246', '249'])).
% 22.85/23.09  thf('251', plain,
% 22.85/23.09      (((k2_pre_topc @ sk_A @ sk_B)
% 22.85/23.09         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 22.85/23.09      inference('demod', [status(thm)], ['104', '109', '110', '111'])).
% 22.85/23.09  thf('252', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.85/23.09      inference('demod', [status(thm)], ['131', '132'])).
% 22.85/23.09  thf('253', plain,
% 22.85/23.09      (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['251', '252'])).
% 22.85/23.09  thf('254', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('255', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 22.85/23.09           = (k3_xboole_0 @ X1 @ X0))),
% 22.85/23.09      inference('sup+', [status(thm)], ['85', '86'])).
% 22.85/23.09  thf('256', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]:
% 22.85/23.09         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 22.85/23.09           = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['254', '255'])).
% 22.85/23.09  thf('257', plain,
% 22.85/23.09      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09         (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 22.85/23.09         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 22.85/23.09      inference('sup+', [status(thm)], ['253', '256'])).
% 22.85/23.09  thf('258', plain,
% 22.85/23.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.85/23.09      inference('sup+', [status(thm)], ['126', '127'])).
% 22.85/23.09  thf('259', plain,
% 22.85/23.09      (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 22.85/23.09      inference('sup+', [status(thm)], ['251', '252'])).
% 22.85/23.09  thf('260', plain,
% 22.85/23.09      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 22.85/23.09         (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 22.85/23.09      inference('demod', [status(thm)], ['257', '258', '259'])).
% 22.85/23.09  thf('261', plain,
% 22.85/23.09      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 22.85/23.09          = (sk_B)))
% 22.85/23.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('sup+', [status(thm)], ['250', '260'])).
% 22.85/23.09  thf('262', plain,
% 22.85/23.09      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 22.85/23.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('sup+', [status(thm)], ['241', '261'])).
% 22.85/23.09  thf('263', plain,
% 22.85/23.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf(fc9_tops_1, axiom,
% 22.85/23.09    (![A:$i,B:$i]:
% 22.85/23.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 22.85/23.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 22.85/23.09       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 22.85/23.09  thf('264', plain,
% 22.85/23.09      (![X59 : $i, X60 : $i]:
% 22.85/23.09         (~ (l1_pre_topc @ X59)
% 22.85/23.09          | ~ (v2_pre_topc @ X59)
% 22.85/23.09          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 22.85/23.09          | (v3_pre_topc @ (k1_tops_1 @ X59 @ X60) @ X59))),
% 22.85/23.09      inference('cnf', [status(esa)], [fc9_tops_1])).
% 22.85/23.09  thf('265', plain,
% 22.85/23.09      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 22.85/23.09        | ~ (v2_pre_topc @ sk_A)
% 22.85/23.09        | ~ (l1_pre_topc @ sk_A))),
% 22.85/23.09      inference('sup-', [status(thm)], ['263', '264'])).
% 22.85/23.09  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('267', plain, ((l1_pre_topc @ sk_A)),
% 22.85/23.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.85/23.09  thf('268', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 22.85/23.09      inference('demod', [status(thm)], ['265', '266', '267'])).
% 22.85/23.09  thf('269', plain,
% 22.85/23.09      (((v3_pre_topc @ sk_B @ sk_A))
% 22.85/23.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 22.85/23.09      inference('sup+', [status(thm)], ['262', '268'])).
% 22.85/23.09  thf('270', plain,
% 22.85/23.09      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 22.85/23.09      inference('split', [status(esa)], ['0'])).
% 22.85/23.09  thf('271', plain,
% 22.85/23.09      (~
% 22.85/23.09       (((k2_tops_1 @ sk_A @ sk_B)
% 22.85/23.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 22.85/23.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 22.85/23.09       ((v3_pre_topc @ sk_B @ sk_A))),
% 22.85/23.09      inference('sup-', [status(thm)], ['269', '270'])).
% 22.85/23.09  thf('272', plain, ($false),
% 22.85/23.09      inference('sat_resolution*', [status(thm)], ['1', '60', '61', '271'])).
% 22.85/23.09  
% 22.85/23.09  % SZS output end Refutation
% 22.85/23.09  
% 22.93/23.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
