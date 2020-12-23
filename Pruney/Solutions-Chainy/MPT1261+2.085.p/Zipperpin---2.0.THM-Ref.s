%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ew3JZOGoXo

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:50 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 230 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  916 (3214 expanded)
%              Number of equality atoms :   70 ( 198 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X18 @ X17 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_pre_topc @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != X28 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('57',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','55','56'])).

thf('58',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('60',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','55'])).

thf('65',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ew3JZOGoXo
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 196 iterations in 0.088s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(t77_tops_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.55             ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55              ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.55                ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.55                  ( k7_subset_1 @
% 0.38/0.55                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(l78_tops_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.55             ( k7_subset_1 @
% 0.38/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X30 : $i, X31 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.38/0.55          | ((k2_tops_1 @ X31 @ X30)
% 0.38/0.55              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.38/0.55                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.38/0.55          | ~ (l1_pre_topc @ X31))),
% 0.38/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.38/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t52_pre_topc, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X28 : $i, X29 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.55          | ~ (v4_pre_topc @ X28 @ X29)
% 0.38/0.55          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.38/0.55          | ~ (l1_pre_topc @ X29))),
% 0.38/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.38/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55              (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (~
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t65_tops_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( k2_pre_topc @ A @ B ) =
% 0.38/0.55             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X32 : $i, X33 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.38/0.55          | ((k2_pre_topc @ X33 @ X32)
% 0.38/0.55              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.38/0.55                 (k2_tops_1 @ X33 @ X32)))
% 0.38/0.55          | ~ (l1_pre_topc @ X33))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.55            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.55         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(dt_k7_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.38/0.55          | (m1_subset_1 @ (k7_subset_1 @ X18 @ X17 @ X19) @ 
% 0.38/0.55             (k1_zfmisc_1 @ X18)))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.38/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['20', '23'])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.38/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.38/0.55          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55            = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.55          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '27'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.38/0.55          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.55  thf(t36_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.38/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.38/0.55  thf(t12_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i]:
% 0.38/0.55         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.55  thf(commutativity_k2_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i]:
% 0.38/0.55         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.38/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.55  thf(l51_zfmisc_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i]:
% 0.38/0.55         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i]:
% 0.38/0.55         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('demod', [status(thm)], ['37', '42'])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.55          = (sk_B)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('demod', [status(thm)], ['28', '43'])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['19', '44'])).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X28 : $i, X29 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.55          | ~ (v2_pre_topc @ X29)
% 0.38/0.55          | ((k2_pre_topc @ X29 @ X28) != (X28))
% 0.38/0.55          | (v4_pre_topc @ X28 @ X29)
% 0.38/0.55          | ~ (l1_pre_topc @ X29))),
% 0.38/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.38/0.55        | ~ (v2_pre_topc @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.55  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['45', '51'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.55       ~
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('57', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['14', '55', '56'])).
% 0.38/0.55  thf('58', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['12', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '58', '59'])).
% 0.38/0.55  thf('61', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55              (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= (~
% 0.38/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('63', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= (~
% 0.38/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      (~
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['14', '55'])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['63', '64'])).
% 0.38/0.55  thf('66', plain, ($false),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['60', '65'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
