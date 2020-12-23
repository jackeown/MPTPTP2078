%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.12OzBBkZs1

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:38 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 301 expanded)
%              Number of leaves         :   44 ( 105 expanded)
%              Depth                    :   18
%              Number of atoms          : 1401 (3177 expanded)
%              Number of equality atoms :  116 ( 220 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('10',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X40 @ X39 ) @ X39 )
      | ~ ( v4_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k1_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('67',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','80'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['86','87'])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('98',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['92','93'])).

thf('102',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','79'])).

thf('104',plain,
    ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','104'])).

thf('106',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','105'])).

thf('107',plain,(
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

thf('108',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_pre_topc @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
       != X33 )
      | ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('116',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.12OzBBkZs1
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.87/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.87/1.07  % Solved by: fo/fo7.sh
% 0.87/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.07  % done 1847 iterations in 0.616s
% 0.87/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.87/1.07  % SZS output start Refutation
% 0.87/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.07  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.87/1.07  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.87/1.07  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.87/1.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.87/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.87/1.07  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.87/1.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.87/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.87/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.87/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.07  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.87/1.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.87/1.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.87/1.07  thf(t77_tops_1, conjecture,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07           ( ( v4_pre_topc @ B @ A ) <=>
% 0.87/1.07             ( ( k2_tops_1 @ A @ B ) =
% 0.87/1.07               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.87/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.07    (~( ![A:$i]:
% 0.87/1.07        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.87/1.07          ( ![B:$i]:
% 0.87/1.07            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07              ( ( v4_pre_topc @ B @ A ) <=>
% 0.87/1.07                ( ( k2_tops_1 @ A @ B ) =
% 0.87/1.07                  ( k7_subset_1 @
% 0.87/1.07                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.87/1.07    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.87/1.07  thf('0', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07              (k1_tops_1 @ sk_A @ sk_B)))
% 0.87/1.07        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('1', plain,
% 0.87/1.07      (~
% 0.87/1.07       (((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.87/1.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.87/1.07      inference('split', [status(esa)], ['0'])).
% 0.87/1.07  thf(commutativity_k2_tarski, axiom,
% 0.87/1.07    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.87/1.07  thf('2', plain,
% 0.87/1.07      (![X16 : $i, X17 : $i]:
% 0.87/1.07         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.87/1.07      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.87/1.07  thf(t12_setfam_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.87/1.07  thf('3', plain,
% 0.87/1.07      (![X28 : $i, X29 : $i]:
% 0.87/1.07         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.87/1.07      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.87/1.07  thf('4', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.07      inference('sup+', [status(thm)], ['2', '3'])).
% 0.87/1.07  thf('5', plain,
% 0.87/1.07      (![X28 : $i, X29 : $i]:
% 0.87/1.07         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.87/1.07      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.87/1.07  thf('6', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.07      inference('sup+', [status(thm)], ['4', '5'])).
% 0.87/1.07  thf('7', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07             (k1_tops_1 @ sk_A @ sk_B)))
% 0.87/1.07        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('8', plain,
% 0.87/1.07      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.87/1.07      inference('split', [status(esa)], ['7'])).
% 0.87/1.07  thf('9', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t69_tops_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( l1_pre_topc @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07           ( ( v4_pre_topc @ B @ A ) =>
% 0.87/1.07             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.87/1.07  thf('10', plain,
% 0.87/1.07      (![X39 : $i, X40 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.87/1.07          | (r1_tarski @ (k2_tops_1 @ X40 @ X39) @ X39)
% 0.87/1.07          | ~ (v4_pre_topc @ X39 @ X40)
% 0.87/1.07          | ~ (l1_pre_topc @ X40))),
% 0.87/1.07      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.87/1.07  thf('11', plain,
% 0.87/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.07        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.87/1.07        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.87/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.07  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('13', plain,
% 0.87/1.07      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.87/1.07        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.87/1.07      inference('demod', [status(thm)], ['11', '12'])).
% 0.87/1.07  thf('14', plain,
% 0.87/1.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.87/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['8', '13'])).
% 0.87/1.07  thf(t28_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.87/1.07  thf('15', plain,
% 0.87/1.07      (![X6 : $i, X7 : $i]:
% 0.87/1.07         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.87/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.07  thf('16', plain,
% 0.87/1.07      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.87/1.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.87/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.07  thf('17', plain,
% 0.87/1.07      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.87/1.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.87/1.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['6', '16'])).
% 0.87/1.07  thf('18', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t74_tops_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( l1_pre_topc @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07           ( ( k1_tops_1 @ A @ B ) =
% 0.87/1.07             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.87/1.07  thf('19', plain,
% 0.87/1.07      (![X41 : $i, X42 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.87/1.07          | ((k1_tops_1 @ X42 @ X41)
% 0.87/1.07              = (k7_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 0.87/1.07                 (k2_tops_1 @ X42 @ X41)))
% 0.87/1.07          | ~ (l1_pre_topc @ X42))),
% 0.87/1.07      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.87/1.07  thf('20', plain,
% 0.87/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.07        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.87/1.07            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.07  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('22', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(redefinition_k7_subset_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.07       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.87/1.07  thf('23', plain,
% 0.87/1.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.87/1.07          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 0.87/1.07      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.87/1.07  thf('24', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.87/1.07           = (k4_xboole_0 @ sk_B @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.07  thf('25', plain,
% 0.87/1.07      (((k1_tops_1 @ sk_A @ sk_B)
% 0.87/1.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.87/1.07      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.87/1.07  thf(t48_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.87/1.07  thf('26', plain,
% 0.87/1.07      (![X12 : $i, X13 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.87/1.07           = (k3_xboole_0 @ X12 @ X13))),
% 0.87/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.87/1.07  thf('27', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.87/1.07         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['25', '26'])).
% 0.87/1.07  thf('28', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.87/1.07           = (k4_xboole_0 @ sk_B @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.07  thf('29', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07              (k1_tops_1 @ sk_A @ sk_B))))
% 0.87/1.07         <= (~
% 0.87/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('split', [status(esa)], ['0'])).
% 0.87/1.07  thf('30', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.87/1.07         <= (~
% 0.87/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['28', '29'])).
% 0.87/1.07  thf('31', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          != (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.87/1.07         <= (~
% 0.87/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['27', '30'])).
% 0.87/1.07  thf('32', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.87/1.07         <= (~
% 0.87/1.07             (((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.87/1.07             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['17', '31'])).
% 0.87/1.07  thf('33', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.87/1.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.87/1.07      inference('simplify', [status(thm)], ['32'])).
% 0.87/1.07  thf('34', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.87/1.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.87/1.07      inference('split', [status(esa)], ['7'])).
% 0.87/1.07  thf('35', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(dt_k2_tops_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( l1_pre_topc @ A ) & 
% 0.87/1.07         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.87/1.07       ( m1_subset_1 @
% 0.87/1.07         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.87/1.07  thf('36', plain,
% 0.87/1.07      (![X35 : $i, X36 : $i]:
% 0.87/1.07         (~ (l1_pre_topc @ X35)
% 0.87/1.07          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.87/1.07          | (m1_subset_1 @ (k2_tops_1 @ X35 @ X36) @ 
% 0.87/1.07             (k1_zfmisc_1 @ (u1_struct_0 @ X35))))),
% 0.87/1.07      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.87/1.07  thf('37', plain,
% 0.87/1.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.87/1.07         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.87/1.07        | ~ (l1_pre_topc @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['35', '36'])).
% 0.87/1.07  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('39', plain,
% 0.87/1.07      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.87/1.07        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('demod', [status(thm)], ['37', '38'])).
% 0.87/1.07  thf('40', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(redefinition_k4_subset_1, axiom,
% 0.87/1.07    (![A:$i,B:$i,C:$i]:
% 0.87/1.07     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.87/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.87/1.07       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.87/1.07  thf('41', plain,
% 0.87/1.07      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.87/1.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.87/1.07          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 0.87/1.07      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.87/1.07  thf('42', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.87/1.07            = (k2_xboole_0 @ sk_B @ X0))
% 0.87/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['40', '41'])).
% 0.87/1.07  thf('43', plain,
% 0.87/1.07      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.87/1.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['39', '42'])).
% 0.87/1.07  thf('44', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t65_tops_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( l1_pre_topc @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07           ( ( k2_pre_topc @ A @ B ) =
% 0.87/1.07             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.87/1.07  thf('45', plain,
% 0.87/1.07      (![X37 : $i, X38 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.87/1.07          | ((k2_pre_topc @ X38 @ X37)
% 0.87/1.07              = (k4_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 0.87/1.07                 (k2_tops_1 @ X38 @ X37)))
% 0.87/1.07          | ~ (l1_pre_topc @ X38))),
% 0.87/1.07      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.87/1.07  thf('46', plain,
% 0.87/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.07        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.87/1.07            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['44', '45'])).
% 0.87/1.07  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('48', plain,
% 0.87/1.07      (((k2_pre_topc @ sk_A @ sk_B)
% 0.87/1.07         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.87/1.07      inference('demod', [status(thm)], ['46', '47'])).
% 0.87/1.07  thf('49', plain,
% 0.87/1.07      (((k2_pre_topc @ sk_A @ sk_B)
% 0.87/1.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['43', '48'])).
% 0.87/1.07  thf('50', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.87/1.07           = (k4_xboole_0 @ sk_B @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.07  thf('51', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07             (k1_tops_1 @ sk_A @ sk_B))))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('split', [status(esa)], ['7'])).
% 0.87/1.07  thf('52', plain,
% 0.87/1.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup+', [status(thm)], ['50', '51'])).
% 0.87/1.07  thf(t36_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.87/1.07  thf('53', plain,
% 0.87/1.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.87/1.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.87/1.07  thf('54', plain,
% 0.87/1.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup+', [status(thm)], ['52', '53'])).
% 0.87/1.07  thf('55', plain,
% 0.87/1.07      (![X6 : $i, X7 : $i]:
% 0.87/1.07         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.87/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.07  thf('56', plain,
% 0.87/1.07      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.87/1.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['54', '55'])).
% 0.87/1.07  thf(t100_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.87/1.07  thf('57', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X4 @ X5)
% 0.87/1.07           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.07  thf('58', plain,
% 0.87/1.07      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.87/1.07          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.87/1.07             (k2_tops_1 @ sk_A @ sk_B))))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup+', [status(thm)], ['56', '57'])).
% 0.87/1.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.87/1.07  thf('59', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.87/1.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.07  thf(t3_subset, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.07  thf('60', plain,
% 0.87/1.07      (![X30 : $i, X32 : $i]:
% 0.87/1.07         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.87/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.07  thf('61', plain,
% 0.87/1.07      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['59', '60'])).
% 0.87/1.07  thf(involutiveness_k3_subset_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.07       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.87/1.07  thf('62', plain,
% 0.87/1.07      (![X20 : $i, X21 : $i]:
% 0.87/1.07         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.87/1.07          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.87/1.07      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.87/1.07  thf('63', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['61', '62'])).
% 0.87/1.07  thf('64', plain,
% 0.87/1.07      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['59', '60'])).
% 0.87/1.07  thf(d5_subset_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.87/1.07       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.87/1.07  thf('65', plain,
% 0.87/1.07      (![X18 : $i, X19 : $i]:
% 0.87/1.07         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.87/1.07          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.87/1.07      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.07  thf('66', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['64', '65'])).
% 0.87/1.07  thf(t3_boole, axiom,
% 0.87/1.07    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.87/1.07  thf('67', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.87/1.07      inference('cnf', [status(esa)], [t3_boole])).
% 0.87/1.07  thf('68', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['66', '67'])).
% 0.87/1.07  thf('69', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.87/1.07      inference('demod', [status(thm)], ['63', '68'])).
% 0.87/1.07  thf(d10_xboole_0, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.07  thf('70', plain,
% 0.87/1.07      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.87/1.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.07  thf('71', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.87/1.07      inference('simplify', [status(thm)], ['70'])).
% 0.87/1.07  thf('72', plain,
% 0.87/1.07      (![X30 : $i, X32 : $i]:
% 0.87/1.07         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.87/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.07  thf('73', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['71', '72'])).
% 0.87/1.07  thf('74', plain,
% 0.87/1.07      (![X18 : $i, X19 : $i]:
% 0.87/1.07         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.87/1.07          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.87/1.07      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.87/1.07  thf('75', plain,
% 0.87/1.07      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['73', '74'])).
% 0.87/1.07  thf(idempotence_k3_xboole_0, axiom,
% 0.87/1.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.87/1.07  thf('76', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.87/1.07  thf('77', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X4 @ X5)
% 0.87/1.07           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.07  thf('78', plain,
% 0.87/1.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['76', '77'])).
% 0.87/1.07  thf('79', plain,
% 0.87/1.07      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['75', '78'])).
% 0.87/1.07  thf('80', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.87/1.07      inference('demod', [status(thm)], ['69', '79'])).
% 0.87/1.07  thf('81', plain,
% 0.87/1.07      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('demod', [status(thm)], ['58', '80'])).
% 0.87/1.07  thf(t98_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.87/1.07  thf('82', plain,
% 0.87/1.07      (![X14 : $i, X15 : $i]:
% 0.87/1.07         ((k2_xboole_0 @ X14 @ X15)
% 0.87/1.07           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.87/1.07  thf('83', plain,
% 0.87/1.07      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.87/1.07          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup+', [status(thm)], ['81', '82'])).
% 0.87/1.07  thf('84', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('85', plain,
% 0.87/1.07      (![X30 : $i, X31 : $i]:
% 0.87/1.07         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.07  thf('86', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['84', '85'])).
% 0.87/1.07  thf('87', plain,
% 0.87/1.07      (![X6 : $i, X7 : $i]:
% 0.87/1.07         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.87/1.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.07  thf('88', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.87/1.07      inference('sup-', [status(thm)], ['86', '87'])).
% 0.87/1.07  thf('89', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X4 @ X5)
% 0.87/1.07           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.07  thf('90', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.87/1.07         = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.87/1.07      inference('sup+', [status(thm)], ['88', '89'])).
% 0.87/1.07  thf('91', plain,
% 0.87/1.07      (![X12 : $i, X13 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.87/1.07           = (k3_xboole_0 @ X12 @ X13))),
% 0.87/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.87/1.07  thf('92', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 0.87/1.07         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['90', '91'])).
% 0.87/1.07  thf('93', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.87/1.07      inference('sup-', [status(thm)], ['86', '87'])).
% 0.87/1.07  thf('94', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)) = (sk_B))),
% 0.87/1.07      inference('demod', [status(thm)], ['92', '93'])).
% 0.87/1.07  thf('95', plain,
% 0.87/1.07      (![X12 : $i, X13 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.87/1.07           = (k3_xboole_0 @ X12 @ X13))),
% 0.87/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.87/1.07  thf('96', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.87/1.07         = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['94', '95'])).
% 0.87/1.07  thf('97', plain,
% 0.87/1.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['76', '77'])).
% 0.87/1.07  thf('98', plain,
% 0.87/1.07      (((k5_xboole_0 @ sk_B @ sk_B)
% 0.87/1.07         = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.87/1.07      inference('demod', [status(thm)], ['96', '97'])).
% 0.87/1.07  thf('99', plain,
% 0.87/1.07      (![X4 : $i, X5 : $i]:
% 0.87/1.07         ((k4_xboole_0 @ X4 @ X5)
% 0.87/1.07           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.87/1.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.07  thf('100', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 0.87/1.07         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.87/1.07      inference('sup+', [status(thm)], ['98', '99'])).
% 0.87/1.07  thf('101', plain,
% 0.87/1.07      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)) = (sk_B))),
% 0.87/1.07      inference('demod', [status(thm)], ['92', '93'])).
% 0.87/1.07  thf('102', plain,
% 0.87/1.07      (((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)) = (sk_B))),
% 0.87/1.07      inference('sup+', [status(thm)], ['100', '101'])).
% 0.87/1.07  thf('103', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.87/1.07      inference('demod', [status(thm)], ['69', '79'])).
% 0.87/1.07  thf('104', plain, (((k5_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 0.87/1.07      inference('demod', [status(thm)], ['102', '103'])).
% 0.87/1.07  thf('105', plain,
% 0.87/1.07      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('demod', [status(thm)], ['83', '104'])).
% 0.87/1.07  thf('106', plain,
% 0.87/1.07      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup+', [status(thm)], ['49', '105'])).
% 0.87/1.07  thf('107', plain,
% 0.87/1.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(t52_pre_topc, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( l1_pre_topc @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.87/1.07           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.87/1.07             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.87/1.07               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.87/1.07  thf('108', plain,
% 0.87/1.07      (![X33 : $i, X34 : $i]:
% 0.87/1.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.87/1.07          | ~ (v2_pre_topc @ X34)
% 0.87/1.07          | ((k2_pre_topc @ X34 @ X33) != (X33))
% 0.87/1.07          | (v4_pre_topc @ X33 @ X34)
% 0.87/1.07          | ~ (l1_pre_topc @ X34))),
% 0.87/1.07      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.87/1.07  thf('109', plain,
% 0.87/1.07      ((~ (l1_pre_topc @ sk_A)
% 0.87/1.07        | (v4_pre_topc @ sk_B @ sk_A)
% 0.87/1.07        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.87/1.07        | ~ (v2_pre_topc @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['107', '108'])).
% 0.87/1.07  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('112', plain,
% 0.87/1.07      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.87/1.07      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.87/1.07  thf('113', plain,
% 0.87/1.07      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['106', '112'])).
% 0.87/1.07  thf('114', plain,
% 0.87/1.07      (((v4_pre_topc @ sk_B @ sk_A))
% 0.87/1.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.87/1.07      inference('simplify', [status(thm)], ['113'])).
% 0.87/1.07  thf('115', plain,
% 0.87/1.07      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.87/1.07      inference('split', [status(esa)], ['0'])).
% 0.87/1.07  thf('116', plain,
% 0.87/1.07      (~
% 0.87/1.07       (((k2_tops_1 @ sk_A @ sk_B)
% 0.87/1.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.87/1.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.87/1.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.87/1.07      inference('sup-', [status(thm)], ['114', '115'])).
% 0.87/1.07  thf('117', plain, ($false),
% 0.87/1.07      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '116'])).
% 0.87/1.07  
% 0.87/1.07  % SZS output end Refutation
% 0.87/1.07  
% 0.87/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
