%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mLDa3Po8vr

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:50 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 382 expanded)
%              Number of leaves         :   36 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          : 1333 (4767 expanded)
%              Number of equality atoms :   97 ( 303 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','51'])).

thf('53',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['11','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X31 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('56',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['6','62'])).

thf('64',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['5','63'])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('69',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( v4_pre_topc @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('80',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('83',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('87',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('89',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('91',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','91'])).

thf('93',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['65','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('95',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('101',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('103',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['6','62','102'])).

thf('104',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['101','103'])).

thf('105',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['64','104'])).

thf('106',plain,(
    $false ),
    inference(simplify,[status(thm)],['105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mLDa3Po8vr
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 1178 iterations in 0.481s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.74/0.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.74/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.74/0.93  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.93  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.74/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.93  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.74/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.74/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.93  thf(t77_tops_1, conjecture,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( v4_pre_topc @ B @ A ) <=>
% 0.74/0.93             ( ( k2_tops_1 @ A @ B ) =
% 0.74/0.93               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i]:
% 0.74/0.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.74/0.93          ( ![B:$i]:
% 0.74/0.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93              ( ( v4_pre_topc @ B @ A ) <=>
% 0.74/0.93                ( ( k2_tops_1 @ A @ B ) =
% 0.74/0.93                  ( k7_subset_1 @
% 0.74/0.93                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93              (k1_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93              (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (~
% 0.74/0.93             (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k7_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.74/0.93          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (~
% 0.74/0.93             (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('demod', [status(thm)], ['1', '4'])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      (~
% 0.74/0.93       (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.74/0.93       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('7', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t65_tops_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( k2_pre_topc @ A @ B ) =
% 0.74/0.93             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      (![X35 : $i, X36 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.74/0.93          | ((k2_pre_topc @ X36 @ X35)
% 0.74/0.93              = (k4_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.74/0.93                 (k2_tops_1 @ X36 @ X35)))
% 0.74/0.93          | ~ (l1_pre_topc @ X36))),
% 0.74/0.93      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.74/0.93            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['7', '8'])).
% 0.74/0.93  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      (((k2_pre_topc @ sk_A @ sk_B)
% 0.74/0.93         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t3_subset, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      (![X28 : $i, X29 : $i]:
% 0.74/0.93         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('14', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('17', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('split', [status(esa)], ['16'])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['15', '17'])).
% 0.74/0.93  thf(t36_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.74/0.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['18', '19'])).
% 0.74/0.93  thf(t1_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.74/0.93       ( r1_tarski @ A @ C ) ))).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.74/0.93         (~ (r1_tarski @ X3 @ X4)
% 0.74/0.93          | ~ (r1_tarski @ X4 @ X5)
% 0.74/0.93          | (r1_tarski @ X3 @ X5))),
% 0.74/0.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      ((![X0 : $i]:
% 0.74/0.93          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.74/0.93           | ~ (r1_tarski @ sk_B @ X0)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['14', '22'])).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      (![X28 : $i, X30 : $i]:
% 0.74/0.93         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('25', plain,
% 0.74/0.93      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.74/0.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['23', '24'])).
% 0.74/0.93  thf('26', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k4_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.74/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.93       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.74/0.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.74/0.93          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93            = (k2_xboole_0 @ sk_B @ X0))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['25', '28'])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['18', '19'])).
% 0.74/0.93  thf(t28_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.74/0.93  thf('31', plain,
% 0.74/0.93      (![X6 : $i, X7 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.74/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.93  thf('32', plain,
% 0.74/0.93      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.74/0.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.74/0.93  thf(t100_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      (![X1 : $i, X2 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X1 @ X2)
% 0.74/0.93           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.93  thf('34', plain,
% 0.74/0.93      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.74/0.93          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.74/0.93             (k2_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['32', '33'])).
% 0.74/0.93  thf(t3_boole, axiom,
% 0.74/0.93    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.93  thf('35', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf(t48_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf('36', plain,
% 0.74/0.93      (![X12 : $i, X13 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.74/0.93           = (k3_xboole_0 @ X12 @ X13))),
% 0.74/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['35', '36'])).
% 0.74/0.93  thf(idempotence_k3_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.74/0.93  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/0.93      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      (![X1 : $i, X2 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X1 @ X2)
% 0.74/0.93           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.93  thf('40', plain,
% 0.74/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['38', '39'])).
% 0.74/0.93  thf(t2_boole, axiom,
% 0.74/0.93    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.93      inference('cnf', [status(esa)], [t2_boole])).
% 0.74/0.93  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/0.93      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.74/0.93  thf('43', plain,
% 0.74/0.93      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('demod', [status(thm)], ['34', '42'])).
% 0.74/0.93  thf(t98_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (![X14 : $i, X15 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X14 @ X15)
% 0.74/0.93           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.74/0.93  thf('45', plain,
% 0.74/0.93      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['43', '44'])).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.93      inference('cnf', [status(esa)], [t2_boole])).
% 0.74/0.93  thf('47', plain,
% 0.74/0.93      (![X1 : $i, X2 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X1 @ X2)
% 0.74/0.93           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.93  thf('48', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['46', '47'])).
% 0.74/0.93  thf('49', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['48', '49'])).
% 0.74/0.93  thf('51', plain,
% 0.74/0.93      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('demod', [status(thm)], ['45', '50'])).
% 0.74/0.93  thf('52', plain,
% 0.74/0.93      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93          = (sk_B)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('demod', [status(thm)], ['29', '51'])).
% 0.74/0.93  thf('53', plain,
% 0.74/0.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['11', '52'])).
% 0.74/0.93  thf('54', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(fc1_tops_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.74/0.93  thf('55', plain,
% 0.74/0.93      (![X31 : $i, X32 : $i]:
% 0.74/0.93         (~ (l1_pre_topc @ X31)
% 0.74/0.93          | ~ (v2_pre_topc @ X31)
% 0.74/0.93          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.74/0.93          | (v4_pre_topc @ (k2_pre_topc @ X31 @ X32) @ X31))),
% 0.74/0.93      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.74/0.93  thf('56', plain,
% 0.74/0.93      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.74/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.74/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['54', '55'])).
% 0.74/0.93  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('59', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.74/0.93      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.74/0.93  thf('60', plain,
% 0.74/0.93      (((v4_pre_topc @ sk_B @ sk_A))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['53', '59'])).
% 0.74/0.93  thf('61', plain,
% 0.74/0.93      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('62', plain,
% 0.74/0.93      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.74/0.93       ~
% 0.74/0.93       (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.93  thf('63', plain,
% 0.74/0.93      (~
% 0.74/0.93       (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('sat_resolution*', [status(thm)], ['6', '62'])).
% 0.74/0.93  thf('64', plain,
% 0.74/0.93      (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('simpl_trail', [status(thm)], ['5', '63'])).
% 0.74/0.93  thf('65', plain,
% 0.74/0.93      (((k2_pre_topc @ sk_A @ sk_B)
% 0.74/0.93         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.74/0.93  thf('66', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.74/0.93  thf('67', plain,
% 0.74/0.93      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('split', [status(esa)], ['16'])).
% 0.74/0.93  thf('68', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t69_tops_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( v4_pre_topc @ B @ A ) =>
% 0.74/0.93             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.74/0.93  thf('69', plain,
% 0.74/0.93      (![X37 : $i, X38 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.74/0.93          | (r1_tarski @ (k2_tops_1 @ X38 @ X37) @ X37)
% 0.74/0.93          | ~ (v4_pre_topc @ X37 @ X38)
% 0.74/0.93          | ~ (l1_pre_topc @ X38))),
% 0.74/0.93      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.74/0.93  thf('70', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.74/0.93        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.74/0.93      inference('sup-', [status(thm)], ['68', '69'])).
% 0.74/0.93  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('72', plain,
% 0.74/0.93      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.74/0.93        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['70', '71'])).
% 0.74/0.93  thf('73', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['67', '72'])).
% 0.74/0.93  thf('74', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.74/0.93         (~ (r1_tarski @ X3 @ X4)
% 0.74/0.93          | ~ (r1_tarski @ X4 @ X5)
% 0.74/0.93          | (r1_tarski @ X3 @ X5))),
% 0.74/0.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.74/0.93  thf('75', plain,
% 0.74/0.93      ((![X0 : $i]:
% 0.74/0.93          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.74/0.93           | ~ (r1_tarski @ sk_B @ X0)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['73', '74'])).
% 0.74/0.93  thf('76', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['66', '75'])).
% 0.74/0.93  thf('77', plain,
% 0.74/0.93      (![X28 : $i, X30 : $i]:
% 0.74/0.93         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('78', plain,
% 0.74/0.93      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.74/0.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['76', '77'])).
% 0.74/0.93  thf('79', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93            = (k2_xboole_0 @ sk_B @ X0))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.74/0.93  thf('80', plain,
% 0.74/0.93      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['78', '79'])).
% 0.74/0.93  thf('81', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['67', '72'])).
% 0.74/0.93  thf('82', plain,
% 0.74/0.93      (![X6 : $i, X7 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.74/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.93  thf('83', plain,
% 0.74/0.93      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.74/0.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['81', '82'])).
% 0.74/0.93  thf('84', plain,
% 0.74/0.93      (![X1 : $i, X2 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X1 @ X2)
% 0.74/0.93           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.93  thf('85', plain,
% 0.74/0.93      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.74/0.93          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.74/0.93             (k2_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['83', '84'])).
% 0.74/0.93  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/0.93      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.74/0.93  thf('87', plain,
% 0.74/0.93      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['85', '86'])).
% 0.74/0.93  thf('88', plain,
% 0.74/0.93      (![X14 : $i, X15 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X14 @ X15)
% 0.74/0.93           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.74/0.93  thf('89', plain,
% 0.74/0.93      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['87', '88'])).
% 0.74/0.93  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['48', '49'])).
% 0.74/0.93  thf('91', plain,
% 0.74/0.93      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['89', '90'])).
% 0.74/0.93  thf('92', plain,
% 0.74/0.93      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93          = (sk_B)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['80', '91'])).
% 0.74/0.93  thf('93', plain,
% 0.74/0.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['65', '92'])).
% 0.74/0.93  thf('94', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(l78_tops_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( k2_tops_1 @ A @ B ) =
% 0.74/0.93             ( k7_subset_1 @
% 0.74/0.93               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.74/0.93               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('95', plain,
% 0.74/0.93      (![X33 : $i, X34 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.74/0.93          | ((k2_tops_1 @ X34 @ X33)
% 0.74/0.93              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.74/0.93                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 0.74/0.93          | ~ (l1_pre_topc @ X34))),
% 0.74/0.93      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.74/0.93  thf('96', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.74/0.93               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['94', '95'])).
% 0.74/0.93  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('98', plain,
% 0.74/0.93      (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.74/0.93            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['96', '97'])).
% 0.74/0.93  thf('99', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['93', '98'])).
% 0.74/0.93  thf('100', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.93  thf('101', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['99', '100'])).
% 0.74/0.93  thf('102', plain,
% 0.74/0.93      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.74/0.93       (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('split', [status(esa)], ['16'])).
% 0.74/0.93  thf('103', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('sat_resolution*', [status(thm)], ['6', '62', '102'])).
% 0.74/0.93  thf('104', plain,
% 0.74/0.93      (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('simpl_trail', [status(thm)], ['101', '103'])).
% 0.74/0.93  thf('105', plain, (((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['64', '104'])).
% 0.74/0.93  thf('106', plain, ($false), inference('simplify', [status(thm)], ['105'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
