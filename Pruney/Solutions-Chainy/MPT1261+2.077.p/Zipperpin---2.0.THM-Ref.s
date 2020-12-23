%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O14QDCbvWq

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 326 expanded)
%              Number of leaves         :   40 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          : 1346 (3550 expanded)
%              Number of equality atoms :  115 ( 268 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X32 @ X31 ) @ X31 )
      | ~ ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('33',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

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
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('51',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('74',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','76'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('81',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('88',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('92',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','96'])).

thf('98',plain,(
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

thf('99',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_pre_topc @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
       != X25 )
      | ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O14QDCbvWq
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:35:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 444 iterations in 0.135s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.62  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.37/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(t77_tops_1, conjecture,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.62             ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.62               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i]:
% 0.37/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62          ( ![B:$i]:
% 0.37/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62              ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.62                ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.62                  ( k7_subset_1 @
% 0.37/0.62                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.37/0.62  thf('0', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62              (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (~
% 0.37/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62             (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['2'])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t69_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v4_pre_topc @ B @ A ) =>
% 0.37/0.62             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X31 : $i, X32 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.37/0.62          | (r1_tarski @ (k2_tops_1 @ X32 @ X31) @ X31)
% 0.37/0.62          | ~ (v4_pre_topc @ X31 @ X32)
% 0.37/0.62          | ~ (l1_pre_topc @ X32))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.62        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.62  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.62        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain,
% 0.37/0.62      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '8'])).
% 0.37/0.62  thf(t28_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X6 : $i, X7 : $i]:
% 0.37/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.62  thf(commutativity_k2_tarski, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.62  thf(t12_setfam_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X23 : $i, X24 : $i]:
% 0.37/0.62         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.37/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X23 : $i, X24 : $i]:
% 0.37/0.62         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.37/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.62  thf(t100_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X1 : $i, X2 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.62          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf(t48_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.62           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t74_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( k1_tops_1 @ A @ B ) =
% 0.37/0.62             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (![X33 : $i, X34 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.37/0.62          | ((k1_tops_1 @ X34 @ X33)
% 0.37/0.62              = (k7_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.37/0.62                 (k2_tops_1 @ X34 @ X33)))
% 0.37/0.62          | ~ (l1_pre_topc @ X34))),
% 0.37/0.62      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.62       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.37/0.62          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.62         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['26', '27', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.62          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62              (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('37', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('38', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.37/0.62             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['34', '37'])).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.62       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['2'])).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62             (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('split', [status(esa)], ['2'])).
% 0.37/0.62  thf('43', plain,
% 0.37/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.62  thf(t36_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.62  thf('44', plain,
% 0.37/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.37/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.62  thf('45', plain,
% 0.37/0.62      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      (![X6 : $i, X7 : $i]:
% 0.37/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.62  thf('47', plain,
% 0.37/0.62      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('49', plain,
% 0.37/0.62      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.62  thf('50', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('51', plain,
% 0.37/0.62      (![X1 : $i, X2 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.62  thf('52', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['50', '51'])).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.37/0.62          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.62             (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['49', '52'])).
% 0.37/0.62  thf('54', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.62           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.62  thf('56', plain,
% 0.37/0.62      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.37/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.62  thf(t12_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.62  thf('57', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.37/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.62  thf('58', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.62  thf(t1_boole, axiom,
% 0.37/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.62  thf('59', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.37/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.62  thf('60', plain,
% 0.37/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.37/0.62  thf('61', plain,
% 0.37/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['55', '60'])).
% 0.37/0.62  thf('62', plain,
% 0.37/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['54', '61'])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      (![X1 : $i, X2 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('65', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.62           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.37/0.62           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['64', '65'])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['54', '61'])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf(t3_boole, axiom,
% 0.37/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.62  thf('70', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.62  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.37/0.62  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['68', '71'])).
% 0.37/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.62  thf('73', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.62  thf('74', plain,
% 0.37/0.62      (![X1 : $i, X2 : $i]:
% 0.37/0.62         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.62  thf('75', plain,
% 0.37/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['73', '74'])).
% 0.37/0.62  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['72', '75'])).
% 0.37/0.62  thf('77', plain,
% 0.37/0.62      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('demod', [status(thm)], ['53', '76'])).
% 0.37/0.62  thf(t39_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.62  thf('78', plain,
% 0.37/0.62      (![X10 : $i, X11 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.37/0.62           = (k2_xboole_0 @ X10 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.62  thf('79', plain,
% 0.37/0.62      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.37/0.62          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['77', '78'])).
% 0.37/0.62  thf('80', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.37/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.62  thf('81', plain,
% 0.37/0.62      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.62  thf('82', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_k2_tops_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( m1_subset_1 @
% 0.37/0.62         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.62  thf('83', plain,
% 0.37/0.62      (![X27 : $i, X28 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X27)
% 0.37/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.37/0.62          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.37/0.62  thf('84', plain,
% 0.37/0.62      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.62  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('86', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['84', '85'])).
% 0.37/0.62  thf('87', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k4_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.62       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.62  thf('88', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.37/0.62          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.37/0.62  thf('89', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.62            = (k2_xboole_0 @ sk_B @ X0))
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.62  thf('90', plain,
% 0.37/0.62      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.62         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['86', '89'])).
% 0.37/0.62  thf('91', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t65_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( k2_pre_topc @ A @ B ) =
% 0.37/0.62             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      (![X29 : $i, X30 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.37/0.62          | ((k2_pre_topc @ X30 @ X29)
% 0.37/0.62              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.37/0.62                 (k2_tops_1 @ X30 @ X29)))
% 0.37/0.62          | ~ (l1_pre_topc @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.37/0.62  thf('93', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.62            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['91', '92'])).
% 0.37/0.62  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('95', plain,
% 0.37/0.62      (((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.62         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.62  thf('96', plain,
% 0.37/0.62      (((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.62         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['90', '95'])).
% 0.37/0.62  thf('97', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['81', '96'])).
% 0.37/0.62  thf('98', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t52_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('99', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.62          | ~ (v2_pre_topc @ X26)
% 0.37/0.62          | ((k2_pre_topc @ X26 @ X25) != (X25))
% 0.37/0.62          | (v4_pre_topc @ X25 @ X26)
% 0.37/0.62          | ~ (l1_pre_topc @ X26))),
% 0.37/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.62  thf('100', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.62        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.37/0.62        | ~ (v2_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.62  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('103', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.37/0.62  thf('104', plain,
% 0.37/0.62      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['97', '103'])).
% 0.37/0.62  thf('105', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_B @ sk_A))
% 0.37/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['104'])).
% 0.37/0.62  thf('106', plain,
% 0.37/0.62      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('107', plain,
% 0.37/0.62      (~
% 0.37/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.62       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.37/0.62  thf('108', plain, ($false),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '107'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
