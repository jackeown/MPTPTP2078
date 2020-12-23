%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TT2DziCkDD

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:48 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 267 expanded)
%              Number of leaves         :   34 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          : 1012 (3418 expanded)
%              Number of equality atoms :   84 ( 230 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_tops_1 @ X30 @ X29 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k2_pre_topc @ X30 @ X29 ) @ ( k1_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','47'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_pre_topc @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
       != X25 )
      | ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('69',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','67','68'])).

thf('70',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('72',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','70','71'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','67'])).

thf('77',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TT2DziCkDD
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:18:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.33/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.53  % Solved by: fo/fo7.sh
% 0.33/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.53  % done 139 iterations in 0.073s
% 0.33/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.53  % SZS output start Refutation
% 0.33/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.33/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.33/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.33/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.33/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.33/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.33/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.33/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.33/0.53  thf(t77_tops_1, conjecture,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.33/0.53             ( ( k2_tops_1 @ A @ B ) =
% 0.33/0.53               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i]:
% 0.33/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.53          ( ![B:$i]:
% 0.33/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53              ( ( v4_pre_topc @ B @ A ) <=>
% 0.33/0.53                ( ( k2_tops_1 @ A @ B ) =
% 0.33/0.53                  ( k7_subset_1 @
% 0.33/0.53                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.33/0.53  thf('0', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(l78_tops_1, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.33/0.53             ( k7_subset_1 @
% 0.33/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.33/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.33/0.53  thf('1', plain,
% 0.33/0.53      (![X29 : $i, X30 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.33/0.53          | ((k2_tops_1 @ X30 @ X29)
% 0.33/0.53              = (k7_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.33/0.53                 (k2_pre_topc @ X30 @ X29) @ (k1_tops_1 @ X30 @ X29)))
% 0.33/0.53          | ~ (l1_pre_topc @ X30))),
% 0.33/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.33/0.53  thf('2', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.53        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.33/0.53               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.33/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.33/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('4', plain,
% 0.33/0.53      (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.53         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.33/0.53            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.33/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.53             (k1_tops_1 @ sk_A @ sk_B)))
% 0.33/0.53        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('6', plain,
% 0.33/0.53      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.33/0.53      inference('split', [status(esa)], ['5'])).
% 0.33/0.53  thf('7', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t52_pre_topc, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.33/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.33/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.33/0.53  thf('8', plain,
% 0.33/0.53      (![X25 : $i, X26 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.33/0.53          | ~ (v4_pre_topc @ X25 @ X26)
% 0.33/0.53          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.33/0.53          | ~ (l1_pre_topc @ X26))),
% 0.33/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.33/0.53  thf('9', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.53        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.33/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.33/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.33/0.53  thf('12', plain,
% 0.33/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.33/0.53         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['6', '11'])).
% 0.33/0.53  thf('13', plain,
% 0.33/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.53          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.53              (k1_tops_1 @ sk_A @ sk_B)))
% 0.33/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (~
% 0.33/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.53             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.33/0.53       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['13'])).
% 0.33/0.53  thf('15', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t65_tops_1, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ( k2_pre_topc @ A @ B ) =
% 0.33/0.53             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (![X31 : $i, X32 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.33/0.53          | ((k2_pre_topc @ X32 @ X31)
% 0.33/0.53              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.33/0.53                 (k2_tops_1 @ X32 @ X31)))
% 0.33/0.53          | ~ (l1_pre_topc @ X32))),
% 0.33/0.53      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.33/0.53  thf('17', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.53        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.33/0.53            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.53               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.33/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.33/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('19', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(dt_k2_tops_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.33/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.33/0.53       ( m1_subset_1 @
% 0.33/0.53         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.33/0.53  thf('20', plain,
% 0.33/0.53      (![X27 : $i, X28 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X27)
% 0.33/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.33/0.53          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.33/0.53      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.33/0.53  thf('21', plain,
% 0.33/0.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.33/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.33/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.33/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('23', plain,
% 0.33/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.33/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('24', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.33/0.53    (![A:$i,B:$i,C:$i]:
% 0.33/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.33/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.33/0.54  thf('25', plain,
% 0.33/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.33/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.33/0.54          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.33/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.33/0.54  thf('26', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.33/0.54            = (k2_xboole_0 @ sk_B @ X0))
% 0.33/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.33/0.54  thf('27', plain,
% 0.33/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.33/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.33/0.54      inference('sup-', [status(thm)], ['23', '26'])).
% 0.33/0.54  thf('28', plain,
% 0.33/0.54      (((k2_pre_topc @ sk_A @ sk_B)
% 0.33/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['17', '18', '27'])).
% 0.33/0.54  thf('29', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.33/0.54    (![A:$i,B:$i,C:$i]:
% 0.33/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.33/0.54  thf('30', plain,
% 0.33/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.33/0.54          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.33/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.33/0.54  thf('31', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.33/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.33/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.33/0.54  thf('32', plain,
% 0.33/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('split', [status(esa)], ['5'])).
% 0.33/0.54  thf('33', plain,
% 0.33/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.33/0.54  thf(t36_xboole_1, axiom,
% 0.33/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.33/0.54  thf('34', plain,
% 0.33/0.54      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.33/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.33/0.54  thf('35', plain,
% 0.33/0.54      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup+', [status(thm)], ['33', '34'])).
% 0.33/0.54  thf(t28_xboole_1, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.33/0.54  thf('36', plain,
% 0.33/0.54      (![X3 : $i, X4 : $i]:
% 0.33/0.54         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.33/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.33/0.54  thf('37', plain,
% 0.33/0.54      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.33/0.54          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.33/0.54  thf(t100_xboole_1, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.54  thf('38', plain,
% 0.33/0.54      (![X1 : $i, X2 : $i]:
% 0.33/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.33/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.33/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.54  thf('39', plain,
% 0.33/0.54      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.33/0.54          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.33/0.54             (k2_tops_1 @ sk_A @ sk_B))))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.33/0.54  thf(t3_boole, axiom,
% 0.33/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.33/0.54  thf('40', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.33/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.33/0.54  thf(t48_xboole_1, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.33/0.54  thf('41', plain,
% 0.33/0.54      (![X9 : $i, X10 : $i]:
% 0.33/0.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.33/0.54           = (k3_xboole_0 @ X9 @ X10))),
% 0.33/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.33/0.54  thf('42', plain,
% 0.33/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.33/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.33/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.33/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.33/0.54  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.33/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.33/0.54  thf('44', plain,
% 0.33/0.54      (![X1 : $i, X2 : $i]:
% 0.33/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.33/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.33/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.54  thf('45', plain,
% 0.33/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.33/0.54      inference('sup+', [status(thm)], ['43', '44'])).
% 0.33/0.54  thf(t2_boole, axiom,
% 0.33/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.33/0.54  thf('46', plain,
% 0.33/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.33/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.33/0.54  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.33/0.54      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.33/0.54  thf('48', plain,
% 0.33/0.54      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('demod', [status(thm)], ['39', '47'])).
% 0.33/0.54  thf(t98_xboole_1, axiom,
% 0.33/0.54    (![A:$i,B:$i]:
% 0.33/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.33/0.54  thf('49', plain,
% 0.33/0.54      (![X11 : $i, X12 : $i]:
% 0.33/0.54         ((k2_xboole_0 @ X11 @ X12)
% 0.33/0.54           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.33/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.33/0.54  thf('50', plain,
% 0.33/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.33/0.54          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup+', [status(thm)], ['48', '49'])).
% 0.33/0.54  thf('51', plain,
% 0.33/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.33/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.33/0.54  thf('52', plain,
% 0.33/0.54      (![X1 : $i, X2 : $i]:
% 0.33/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.33/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.33/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.54  thf('53', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.33/0.54      inference('sup+', [status(thm)], ['51', '52'])).
% 0.33/0.54  thf('54', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.33/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.33/0.54  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.33/0.54      inference('sup+', [status(thm)], ['53', '54'])).
% 0.33/0.54  thf('56', plain,
% 0.33/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('demod', [status(thm)], ['50', '55'])).
% 0.33/0.54  thf('57', plain,
% 0.33/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup+', [status(thm)], ['28', '56'])).
% 0.33/0.54  thf('58', plain,
% 0.33/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('59', plain,
% 0.33/0.54      (![X25 : $i, X26 : $i]:
% 0.33/0.54         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.33/0.54          | ~ (v2_pre_topc @ X26)
% 0.33/0.54          | ((k2_pre_topc @ X26 @ X25) != (X25))
% 0.33/0.54          | (v4_pre_topc @ X25 @ X26)
% 0.33/0.54          | ~ (l1_pre_topc @ X26))),
% 0.33/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.33/0.54  thf('60', plain,
% 0.33/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.54        | (v4_pre_topc @ sk_B @ sk_A)
% 0.33/0.54        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.33/0.54        | ~ (v2_pre_topc @ sk_A))),
% 0.33/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.33/0.54  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.54  thf('63', plain,
% 0.33/0.54      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.33/0.54  thf('64', plain,
% 0.33/0.54      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['57', '63'])).
% 0.33/0.54  thf('65', plain,
% 0.33/0.54      (((v4_pre_topc @ sk_B @ sk_A))
% 0.33/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('simplify', [status(thm)], ['64'])).
% 0.33/0.54  thf('66', plain,
% 0.33/0.54      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.33/0.54      inference('split', [status(esa)], ['13'])).
% 0.33/0.54  thf('67', plain,
% 0.33/0.54      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.33/0.54       ~
% 0.33/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.33/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.33/0.54  thf('68', plain,
% 0.33/0.54      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.33/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.33/0.54      inference('split', [status(esa)], ['5'])).
% 0.33/0.54  thf('69', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.54      inference('sat_resolution*', [status(thm)], ['14', '67', '68'])).
% 0.33/0.54  thf('70', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.33/0.54      inference('simpl_trail', [status(thm)], ['12', '69'])).
% 0.33/0.54  thf('71', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.33/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.33/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.33/0.54  thf('72', plain,
% 0.33/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.33/0.54      inference('demod', [status(thm)], ['4', '70', '71'])).
% 0.33/0.54  thf('73', plain,
% 0.33/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54              (k1_tops_1 @ sk_A @ sk_B))))
% 0.33/0.54         <= (~
% 0.33/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('split', [status(esa)], ['13'])).
% 0.33/0.54  thf('74', plain,
% 0.33/0.54      (![X0 : $i]:
% 0.33/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.33/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.33/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.33/0.54  thf('75', plain,
% 0.33/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.33/0.54         <= (~
% 0.33/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.33/0.54      inference('demod', [status(thm)], ['73', '74'])).
% 0.33/0.54  thf('76', plain,
% 0.33/0.54      (~
% 0.33/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.33/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.33/0.54      inference('sat_resolution*', [status(thm)], ['14', '67'])).
% 0.33/0.54  thf('77', plain,
% 0.33/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.33/0.54         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.33/0.54      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.33/0.54  thf('78', plain, ($false),
% 0.33/0.54      inference('simplify_reflect-', [status(thm)], ['72', '77'])).
% 0.33/0.54  
% 0.33/0.54  % SZS output end Refutation
% 0.33/0.54  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
