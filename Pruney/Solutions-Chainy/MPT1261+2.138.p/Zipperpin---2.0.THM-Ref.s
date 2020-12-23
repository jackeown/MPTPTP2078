%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjiRc2KY0N

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 301 expanded)
%              Number of leaves         :   35 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          : 1091 (3964 expanded)
%              Number of equality atoms :   91 ( 270 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('40',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('59',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_pre_topc @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
       != X25 )
      | ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('72',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','70','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('75',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','73','74'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','70'])).

thf('80',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bjiRc2KY0N
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 153 iterations in 0.066s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(t77_tops_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.53             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.53               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.53                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.53                  ( k7_subset_1 @
% 0.20/0.53                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l78_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.53             ( k7_subset_1 @
% 0.20/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.20/0.53          | ((k2_tops_1 @ X30 @ X29)
% 0.20/0.53              = (k7_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.20/0.53                 (k2_pre_topc @ X30 @ X29) @ (k1_tops_1 @ X30 @ X29)))
% 0.20/0.53          | ~ (l1_pre_topc @ X30))),
% 0.20/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.53            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t52_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.53          | ~ (v4_pre_topc @ X25 @ X26)
% 0.20/0.53          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.20/0.53          | ~ (l1_pre_topc @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.53         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t65_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.53             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.20/0.53          | ((k2_pre_topc @ X32 @ X31)
% 0.20/0.53              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.20/0.53                 (k2_tops_1 @ X32 @ X31)))
% 0.20/0.53          | ~ (l1_pre_topc @ X32))),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.53            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k2_tops_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X27)
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.53          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.20/0.53          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.53         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.53         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.20/0.53          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(t48_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.20/0.53           = (k3_xboole_0 @ X17 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.53          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf(t47_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.20/0.53           = (k4_xboole_0 @ X15 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.20/0.53           = (k3_xboole_0 @ X17 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.53          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.53           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.53          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.53             (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['40', '43'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('46', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('48', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X5 : $i, X7 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['50', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '54'])).
% 0.20/0.53  thf(t39_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.20/0.53           = (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.20/0.53          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf(t1_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('58', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['28', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.53          | ~ (v2_pre_topc @ X26)
% 0.20/0.53          | ((k2_pre_topc @ X26 @ X25) != (X25))
% 0.20/0.53          | (v4_pre_topc @ X25 @ X26)
% 0.20/0.53          | ~ (l1_pre_topc @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.53       ~
% 0.20/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('72', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['14', '70', '71'])).
% 0.20/0.53  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['12', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['4', '73', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['13'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['14', '70'])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
