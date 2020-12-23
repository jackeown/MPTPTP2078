%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jnxs3LhGXR

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:51 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 303 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          : 1056 (4028 expanded)
%              Number of equality atoms :   70 ( 217 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k4_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('54',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X27 @ X28 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('66',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['63','69'])).

thf('71',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('72',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('74',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['44','72','73'])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['42','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('77',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['44','72'])).

thf('82',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jnxs3LhGXR
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 1188 iterations in 0.475s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.69/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.89  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.69/0.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.69/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.69/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.89  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.69/0.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.69/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.89  thf(t77_tops_1, conjecture,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89           ( ( v4_pre_topc @ B @ A ) <=>
% 0.69/0.89             ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.89               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i]:
% 0.69/0.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.89          ( ![B:$i]:
% 0.69/0.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89              ( ( v4_pre_topc @ B @ A ) <=>
% 0.69/0.89                ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.89                  ( k7_subset_1 @
% 0.69/0.89                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(l78_tops_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( l1_pre_topc @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89           ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.89             ( k7_subset_1 @
% 0.69/0.89               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.69/0.89               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      (![X29 : $i, X30 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.89          | ((k2_tops_1 @ X30 @ X29)
% 0.69/0.89              = (k7_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.69/0.89                 (k2_pre_topc @ X30 @ X29) @ (k1_tops_1 @ X30 @ X29)))
% 0.69/0.89          | ~ (l1_pre_topc @ X30))),
% 0.69/0.89      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.89               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.89  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('4', plain,
% 0.69/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.69/0.89            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t65_tops_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( l1_pre_topc @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89           ( ( k2_pre_topc @ A @ B ) =
% 0.69/0.89             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.89  thf('6', plain,
% 0.69/0.89      (![X31 : $i, X32 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.69/0.89          | ((k2_pre_topc @ X32 @ X31)
% 0.69/0.89              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.69/0.89                 (k2_tops_1 @ X32 @ X31)))
% 0.69/0.89          | ~ (l1_pre_topc @ X32))),
% 0.69/0.89      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.69/0.89  thf('7', plain,
% 0.69/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.69/0.89            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.89  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.69/0.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)], ['7', '8'])).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89             (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.89        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('11', plain,
% 0.69/0.89      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('split', [status(esa)], ['10'])).
% 0.69/0.89  thf('12', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t69_tops_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( l1_pre_topc @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.89           ( ( v4_pre_topc @ B @ A ) =>
% 0.69/0.89             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X33 : $i, X34 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.69/0.89          | (r1_tarski @ (k2_tops_1 @ X34 @ X33) @ X33)
% 0.69/0.89          | ~ (v4_pre_topc @ X33 @ X34)
% 0.69/0.89          | ~ (l1_pre_topc @ X34))),
% 0.69/0.89      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.89        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.69/0.89        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.89  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('16', plain,
% 0.69/0.89      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.69/0.89        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['11', '16'])).
% 0.69/0.89  thf(t28_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.89  thf('18', plain,
% 0.69/0.89      (![X12 : $i, X13 : $i]:
% 0.69/0.89         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.69/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.69/0.89  thf('19', plain,
% 0.69/0.89      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.69/0.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.69/0.89  thf('20', plain,
% 0.69/0.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.89          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['19', '20'])).
% 0.69/0.89  thf(t48_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X16 : $i, X17 : $i]:
% 0.69/0.89         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.69/0.89           = (k3_xboole_0 @ X16 @ X17))),
% 0.69/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t3_subset, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (![X24 : $i, X25 : $i]:
% 0.69/0.89         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.89  thf('25', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.69/0.89  thf(t109_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ (k4_xboole_0 @ X7 @ X9) @ X8))),
% 0.69/0.89      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X24 : $i, X26 : $i]:
% 0.69/0.89         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.69/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.69/0.89          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.69/0.89          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['22', '29'])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['21', '30'])).
% 0.69/0.89  thf('32', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(redefinition_k4_subset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.69/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.89       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.69/0.89          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.69/0.89          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.69/0.89  thf('34', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.89            = (k2_xboole_0 @ sk_B @ X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.89          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['31', '34'])).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['11', '16'])).
% 0.69/0.89  thf(t12_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i]:
% 0.69/0.89         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.69/0.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['36', '37'])).
% 0.69/0.89  thf(commutativity_k2_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.89  thf('40', plain,
% 0.69/0.89      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['38', '39'])).
% 0.69/0.89  thf('41', plain,
% 0.69/0.89      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.89          = (sk_B)))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['35', '40'])).
% 0.69/0.89  thf('42', plain,
% 0.69/0.89      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.69/0.89         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['9', '41'])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89              (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.89        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('44', plain,
% 0.69/0.89      (~
% 0.69/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.69/0.89       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.89      inference('split', [status(esa)], ['43'])).
% 0.69/0.89  thf('45', plain,
% 0.69/0.89      (((k2_pre_topc @ sk_A @ sk_B)
% 0.69/0.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)], ['7', '8'])).
% 0.69/0.89  thf('46', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(redefinition_k7_subset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.89       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.69/0.89          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.69/0.89  thf('48', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.89           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.69/0.89  thf('49', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89             (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('split', [status(esa)], ['10'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.69/0.89          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['50', '51'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.89            = (k2_xboole_0 @ sk_B @ X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.69/0.89  thf('54', plain,
% 0.69/0.89      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.89          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['52', '53'])).
% 0.69/0.89  thf('55', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.89  thf(t36_xboole_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.69/0.89  thf('56', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.69/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (![X10 : $i, X11 : $i]:
% 0.69/0.89         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.69/0.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.69/0.89  thf('58', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.89  thf('59', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['58', '59'])).
% 0.69/0.89  thf('61', plain,
% 0.69/0.89      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['55', '60'])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.89          = (sk_B)))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('demod', [status(thm)], ['54', '61'])).
% 0.69/0.89  thf('63', plain,
% 0.69/0.89      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['45', '62'])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(fc1_tops_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.69/0.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.89       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.69/0.89  thf('65', plain,
% 0.69/0.89      (![X27 : $i, X28 : $i]:
% 0.69/0.89         (~ (l1_pre_topc @ X27)
% 0.69/0.89          | ~ (v2_pre_topc @ X27)
% 0.69/0.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.69/0.89          | (v4_pre_topc @ (k2_pre_topc @ X27 @ X28) @ X27))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.69/0.89  thf('66', plain,
% 0.69/0.89      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.69/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.89  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('69', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.69/0.89      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.69/0.89  thf('70', plain,
% 0.69/0.89      (((v4_pre_topc @ sk_B @ sk_A))
% 0.69/0.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('sup+', [status(thm)], ['63', '69'])).
% 0.69/0.89  thf('71', plain,
% 0.69/0.89      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.89      inference('split', [status(esa)], ['43'])).
% 0.69/0.89  thf('72', plain,
% 0.69/0.89      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.69/0.89       ~
% 0.69/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['70', '71'])).
% 0.69/0.89  thf('73', plain,
% 0.69/0.89      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.69/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.89      inference('split', [status(esa)], ['10'])).
% 0.69/0.89  thf('74', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['44', '72', '73'])).
% 0.69/0.89  thf('75', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['42', '74'])).
% 0.69/0.89  thf('76', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.89           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.69/0.89  thf('77', plain,
% 0.69/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('demod', [status(thm)], ['4', '75', '76'])).
% 0.69/0.89  thf('78', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89              (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('split', [status(esa)], ['43'])).
% 0.69/0.89  thf('79', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.89           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.89         <= (~
% 0.69/0.89             (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.89      inference('demod', [status(thm)], ['78', '79'])).
% 0.69/0.89  thf('81', plain,
% 0.69/0.89      (~
% 0.69/0.89       (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.89             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.89      inference('sat_resolution*', [status(thm)], ['44', '72'])).
% 0.69/0.89  thf('82', plain,
% 0.69/0.89      (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.89         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.69/0.89  thf('83', plain, ($false),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
