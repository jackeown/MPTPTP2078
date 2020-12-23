%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Izst3jxfZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:46 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 226 expanded)
%              Number of leaves         :   40 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          : 1234 (2631 expanded)
%              Number of equality atoms :   96 ( 172 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( v4_pre_topc @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('62',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('67',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('69',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('75',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','78'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('81',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('83',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','83'])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
       != X31 )
      | ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Izst3jxfZ
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 646 iterations in 0.167s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.63  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.63  thf(t77_tops_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.63             ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.63               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63              ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.63                ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.63                  ( k7_subset_1 @
% 0.45/0.63                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63              (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (~
% 0.45/0.63       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf(commutativity_k2_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i]:
% 0.45/0.63         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.63  thf(t12_setfam_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X26 : $i, X27 : $i]:
% 0.45/0.63         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.45/0.63      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X26 : $i, X27 : $i]:
% 0.45/0.63         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.45/0.63      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t69_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.63             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X37 : $i, X38 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.45/0.63          | (r1_tarski @ (k2_tops_1 @ X38 @ X37) @ X37)
% 0.45/0.63          | ~ (v4_pre_topc @ X37 @ X38)
% 0.45/0.63          | ~ (l1_pre_topc @ X38))),
% 0.45/0.63      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '13'])).
% 0.45/0.63  thf(t28_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.45/0.63          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['6', '16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t74_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.63             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X39 : $i, X40 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.45/0.63          | ((k1_tops_1 @ X40 @ X39)
% 0.45/0.63              = (k7_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 0.45/0.63                 (k2_tops_1 @ X40 @ X39)))
% 0.45/0.63          | ~ (l1_pre_topc @ X40))),
% 0.45/0.63      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.63            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k7_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.45/0.63          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.63         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.45/0.63  thf(t48_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.63           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.63         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63              (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.45/0.63             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('split', [status(esa)], ['7'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k2_tops_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @
% 0.45/0.63         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X33 : $i, X34 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ X33)
% 0.45/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.45/0.63          | (m1_subset_1 @ (k2_tops_1 @ X33 @ X34) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X33))))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X28 : $i, X29 : $i]:
% 0.45/0.63         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.63         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.63           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.63  thf(t36_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.45/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (![X28 : $i, X30 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['46', '49'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.45/0.63          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63            = (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.45/0.63           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['50', '53'])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63         = (k2_xboole_0 @ sk_B @ 
% 0.45/0.63            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['45', '54'])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t65_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( k2_pre_topc @ A @ B ) =
% 0.45/0.63             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('57', plain,
% 0.45/0.63      (![X35 : $i, X36 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.63          | ((k2_pre_topc @ X36 @ X35)
% 0.45/0.63              = (k4_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.45/0.63                 (k2_tops_1 @ X36 @ X35)))
% 0.45/0.63          | ~ (l1_pre_topc @ X36))),
% 0.45/0.63      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.63            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.63  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.63         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.63         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['55', '60', '61'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('split', [status(esa)], ['7'])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.45/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i]:
% 0.45/0.63         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.45/0.63          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf(t100_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (![X1 : $i, X2 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X1 @ X2)
% 0.45/0.63           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.45/0.63          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.63             (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.45/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.63  thf('72', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (![X1 : $i, X2 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X1 @ X2)
% 0.45/0.63           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.63  thf(t1_boole, axiom,
% 0.45/0.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.63  thf('75', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.63  thf(t46_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.45/0.63  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['75', '76'])).
% 0.45/0.63  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['74', '77'])).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['71', '78'])).
% 0.45/0.63  thf(t39_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.63  thf('80', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.45/0.63           = (k2_xboole_0 @ X8 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.45/0.63          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['79', '80'])).
% 0.45/0.63  thf('82', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['62', '83'])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t52_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.63             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.63               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('86', plain,
% 0.45/0.63      (![X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.45/0.63          | ~ (v2_pre_topc @ X32)
% 0.45/0.63          | ((k2_pre_topc @ X32 @ X31) != (X31))
% 0.45/0.63          | (v4_pre_topc @ X31 @ X32)
% 0.45/0.63          | ~ (l1_pre_topc @ X32))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.63  thf('87', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.45/0.63        | ~ (v2_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.63  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('90', plain,
% 0.45/0.63      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.45/0.63  thf('91', plain,
% 0.45/0.63      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['84', '90'])).
% 0.45/0.63  thf('92', plain,
% 0.45/0.63      (((v4_pre_topc @ sk_B @ sk_A))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['91'])).
% 0.45/0.63  thf('93', plain,
% 0.45/0.63      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('94', plain,
% 0.45/0.63      (~
% 0.45/0.63       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.63  thf('95', plain, ($false),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '94'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
