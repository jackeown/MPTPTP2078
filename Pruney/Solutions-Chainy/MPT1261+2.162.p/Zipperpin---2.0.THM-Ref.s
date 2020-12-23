%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nnh8uqYRKW

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:02 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 262 expanded)
%              Number of leaves         :   31 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  955 (3334 expanded)
%              Number of equality atoms :   71 ( 204 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_tops_1 @ X23 @ X22 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k2_pre_topc @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != X18 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('66',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','64','65'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('69',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','67','68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','64'])).

thf('74',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nnh8uqYRKW
% 0.14/0.37  % Computer   : n014.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 152 iterations in 0.064s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.24/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.24/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.24/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.24/0.54  thf(t77_tops_1, conjecture,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.54       ( ![B:$i]:
% 0.24/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.54           ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.54               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i]:
% 0.24/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.54          ( ![B:$i]:
% 0.24/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.54              ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.54                  ( k7_subset_1 @
% 0.24/0.54                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.24/0.54  thf('0', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(l78_tops_1, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( l1_pre_topc @ A ) =>
% 0.24/0.54       ( ![B:$i]:
% 0.24/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.54             ( k7_subset_1 @
% 0.24/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.24/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.54  thf('1', plain,
% 0.24/0.54      (![X22 : $i, X23 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.24/0.54          | ((k2_tops_1 @ X23 @ X22)
% 0.24/0.54              = (k7_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.24/0.54                 (k2_pre_topc @ X23 @ X22) @ (k1_tops_1 @ X23 @ X22)))
% 0.24/0.54          | ~ (l1_pre_topc @ X23))),
% 0.24/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.24/0.54  thf('2', plain,
% 0.24/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.54  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('4', plain,
% 0.24/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.24/0.54            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54             (k1_tops_1 @ sk_A @ sk_B)))
% 0.24/0.54        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('6', plain,
% 0.24/0.54      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.54      inference('split', [status(esa)], ['5'])).
% 0.24/0.54  thf('7', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(t52_pre_topc, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( l1_pre_topc @ A ) =>
% 0.24/0.54       ( ![B:$i]:
% 0.24/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.54           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.24/0.54             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.24/0.54               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.24/0.54  thf('8', plain,
% 0.24/0.54      (![X18 : $i, X19 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.24/0.54          | ~ (v4_pre_topc @ X18 @ X19)
% 0.24/0.54          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 0.24/0.54          | ~ (l1_pre_topc @ X19))),
% 0.24/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.24/0.54  thf('9', plain,
% 0.24/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.54        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.24/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.54  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.54  thf('12', plain,
% 0.24/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.24/0.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['6', '11'])).
% 0.24/0.54  thf('13', plain,
% 0.24/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54              (k1_tops_1 @ sk_A @ sk_B)))
% 0.24/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('14', plain,
% 0.24/0.54      (~
% 0.24/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.24/0.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.54      inference('split', [status(esa)], ['13'])).
% 0.24/0.54  thf('15', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(t65_tops_1, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( l1_pre_topc @ A ) =>
% 0.24/0.54       ( ![B:$i]:
% 0.24/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.54           ( ( k2_pre_topc @ A @ B ) =
% 0.24/0.54             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.54  thf('16', plain,
% 0.24/0.54      (![X24 : $i, X25 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.24/0.54          | ((k2_pre_topc @ X25 @ X24)
% 0.24/0.54              = (k4_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 0.24/0.54                 (k2_tops_1 @ X25 @ X24)))
% 0.24/0.54          | ~ (l1_pre_topc @ X25))),
% 0.24/0.54      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.24/0.54  thf('17', plain,
% 0.24/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.54        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.24/0.54            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('19', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(dt_k2_tops_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.24/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.54       ( m1_subset_1 @
% 0.24/0.54         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.54  thf('20', plain,
% 0.24/0.54      (![X20 : $i, X21 : $i]:
% 0.24/0.54         (~ (l1_pre_topc @ X20)
% 0.24/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.24/0.54          | (m1_subset_1 @ (k2_tops_1 @ X20 @ X21) @ 
% 0.24/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.24/0.54      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.24/0.54  thf('21', plain,
% 0.24/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.54  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('23', plain,
% 0.24/0.54      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.24/0.54  thf('24', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.24/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.24/0.54  thf('25', plain,
% 0.24/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.24/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.24/0.54          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.24/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.24/0.54  thf('26', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.54            = (k2_xboole_0 @ sk_B @ X0))
% 0.24/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.54  thf('27', plain,
% 0.24/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.24/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['23', '26'])).
% 0.24/0.54  thf('28', plain,
% 0.24/0.54      (((k2_pre_topc @ sk_A @ sk_B)
% 0.24/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.54      inference('demod', [status(thm)], ['17', '18', '27'])).
% 0.24/0.54  thf('29', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.24/0.54  thf('30', plain,
% 0.24/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.24/0.54          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.24/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.24/0.54  thf('31', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.54  thf('32', plain,
% 0.24/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('split', [status(esa)], ['5'])).
% 0.24/0.54  thf('33', plain,
% 0.24/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.24/0.54  thf(t36_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.24/0.54  thf('34', plain,
% 0.24/0.54      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.24/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.24/0.54  thf('35', plain,
% 0.24/0.54      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['33', '34'])).
% 0.24/0.54  thf(t1_boole, axiom,
% 0.24/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.54  thf('36', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.54  thf(t43_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.24/0.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.24/0.54  thf('37', plain,
% 0.24/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.54         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.24/0.54          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.24/0.54  thf('38', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r1_tarski @ X1 @ X0)
% 0.24/0.54          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.24/0.54  thf('39', plain,
% 0.24/0.54      (((r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.24/0.54         k1_xboole_0))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['35', '38'])).
% 0.24/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.54  thf('40', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.24/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.54  thf(d10_xboole_0, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.54  thf('41', plain,
% 0.24/0.54      (![X0 : $i, X2 : $i]:
% 0.24/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.54  thf('42', plain,
% 0.24/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.54  thf('43', plain,
% 0.24/0.54      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['39', '42'])).
% 0.24/0.54  thf(t98_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.24/0.54  thf('44', plain,
% 0.24/0.54      (![X10 : $i, X11 : $i]:
% 0.24/0.54         ((k2_xboole_0 @ X10 @ X11)
% 0.24/0.54           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.24/0.54  thf('45', plain,
% 0.24/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.24/0.54          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['43', '44'])).
% 0.24/0.54  thf('46', plain,
% 0.24/0.54      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.24/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.24/0.54  thf('47', plain,
% 0.24/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.54  thf('48', plain,
% 0.24/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.24/0.54  thf('49', plain,
% 0.24/0.54      (![X10 : $i, X11 : $i]:
% 0.24/0.54         ((k2_xboole_0 @ X10 @ X11)
% 0.24/0.54           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.24/0.54  thf('50', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['48', '49'])).
% 0.24/0.54  thf('51', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.54  thf('52', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['50', '51'])).
% 0.24/0.54  thf('53', plain,
% 0.24/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('demod', [status(thm)], ['45', '52'])).
% 0.24/0.54  thf('54', plain,
% 0.24/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['28', '53'])).
% 0.24/0.54  thf('55', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('56', plain,
% 0.24/0.54      (![X18 : $i, X19 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.24/0.54          | ~ (v2_pre_topc @ X19)
% 0.24/0.54          | ((k2_pre_topc @ X19 @ X18) != (X18))
% 0.24/0.54          | (v4_pre_topc @ X18 @ X19)
% 0.24/0.54          | ~ (l1_pre_topc @ X19))),
% 0.24/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.24/0.54  thf('57', plain,
% 0.24/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.54        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.54        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.24/0.54        | ~ (v2_pre_topc @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.24/0.54  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('60', plain,
% 0.24/0.54      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.24/0.54      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.24/0.54  thf('61', plain,
% 0.24/0.54      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['54', '60'])).
% 0.24/0.54  thf('62', plain,
% 0.24/0.54      (((v4_pre_topc @ sk_B @ sk_A))
% 0.24/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('simplify', [status(thm)], ['61'])).
% 0.24/0.54  thf('63', plain,
% 0.24/0.54      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.54      inference('split', [status(esa)], ['13'])).
% 0.24/0.54  thf('64', plain,
% 0.24/0.54      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.24/0.54       ~
% 0.24/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.24/0.54  thf('65', plain,
% 0.24/0.54      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.24/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.54      inference('split', [status(esa)], ['5'])).
% 0.24/0.54  thf('66', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.54      inference('sat_resolution*', [status(thm)], ['14', '64', '65'])).
% 0.24/0.54  thf('67', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.24/0.54      inference('simpl_trail', [status(thm)], ['12', '66'])).
% 0.24/0.54  thf('68', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.54  thf('69', plain,
% 0.24/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.54      inference('demod', [status(thm)], ['4', '67', '68'])).
% 0.24/0.54  thf('70', plain,
% 0.24/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54              (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.54         <= (~
% 0.24/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('split', [status(esa)], ['13'])).
% 0.24/0.54  thf('71', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.54  thf('72', plain,
% 0.24/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.54         <= (~
% 0.24/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.54      inference('demod', [status(thm)], ['70', '71'])).
% 0.24/0.54  thf('73', plain,
% 0.24/0.54      (~
% 0.24/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.54      inference('sat_resolution*', [status(thm)], ['14', '64'])).
% 0.24/0.54  thf('74', plain,
% 0.24/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.54         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.54      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 0.24/0.54  thf('75', plain, ($false),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['69', '74'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
