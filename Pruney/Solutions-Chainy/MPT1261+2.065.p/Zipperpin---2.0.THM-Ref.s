%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzR7DiJ2c8

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:47 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 273 expanded)
%              Number of leaves         :   32 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  889 (3514 expanded)
%              Number of equality atoms :   62 ( 201 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('47',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('53',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('55',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['12','53','54'])).

thf('56',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['10','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8','56'])).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','25'])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('67',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','65','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['12','53'])).

thf('72',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzR7DiJ2c8
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 153 iterations in 0.077s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.35/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.54  thf(t77_tops_1, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( v4_pre_topc @ B @ A ) <=>
% 0.35/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.35/0.54               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54              ( ( v4_pre_topc @ B @ A ) <=>
% 0.35/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.35/0.54                  ( k7_subset_1 @
% 0.35/0.54                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l78_tops_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.35/0.54             ( k7_subset_1 @
% 0.35/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.35/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.35/0.54          | ((k2_tops_1 @ X25 @ X24)
% 0.35/0.54              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.35/0.54                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 0.35/0.54          | ~ (l1_pre_topc @ X25))),
% 0.35/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.54  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.35/0.54            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t69_tops_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( v4_pre_topc @ B @ A ) =>
% 0.35/0.54             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X28 : $i, X29 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.35/0.54          | (r1_tarski @ (k2_tops_1 @ X29 @ X28) @ X28)
% 0.35/0.54          | ~ (v4_pre_topc @ X28 @ X29)
% 0.35/0.54          | ~ (l1_pre_topc @ X29))),
% 0.35/0.54      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.35/0.54        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.54        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['9'])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54              (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (~
% 0.35/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.35/0.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('split', [status(esa)], ['11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t65_tops_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( k2_pre_topc @ A @ B ) =
% 0.35/0.54             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X26 : $i, X27 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.35/0.54          | ((k2_pre_topc @ X27 @ X26)
% 0.35/0.54              = (k4_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.35/0.54                 (k2_tops_1 @ X27 @ X26)))
% 0.35/0.54          | ~ (l1_pre_topc @ X27))),
% 0.35/0.54      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.35/0.54            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_k2_tops_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( m1_subset_1 @
% 0.35/0.54         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X20 : $i, X21 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X20)
% 0.35/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.35/0.54          | (m1_subset_1 @ (k2_tops_1 @ X20 @ X21) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.35/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.35/0.54          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54            = (k2_xboole_0 @ sk_B @ X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.35/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['21', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_B)
% 0.35/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['15', '16', '25'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.35/0.54          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('split', [status(esa)], ['9'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf(t36_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.35/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.35/0.54  thf(t28_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]:
% 0.35/0.54         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.35/0.54           = (k4_xboole_0 @ X0 @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf(commutativity_k2_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.54  thf(t12_setfam_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i]:
% 0.35/0.54         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i]:
% 0.35/0.54         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.54           = (k4_xboole_0 @ X0 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '39'])).
% 0.35/0.54  thf(t22_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.54  thf('41', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.35/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['31', '42'])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['26', '43'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(fc1_tops_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      (![X22 : $i, X23 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X22)
% 0.35/0.54          | ~ (v2_pre_topc @ X22)
% 0.35/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.35/0.54          | (v4_pre_topc @ (k2_pre_topc @ X22 @ X23) @ X22))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.54  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('50', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (((v4_pre_topc @ sk_B @ sk_A))
% 0.35/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('sup+', [status(thm)], ['44', '50'])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['11'])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.35/0.54       ~
% 0.35/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.35/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('split', [status(esa)], ['9'])).
% 0.35/0.54  thf('55', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['12', '53', '54'])).
% 0.35/0.54  thf('56', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['10', '55'])).
% 0.35/0.54  thf('57', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.35/0.54      inference('demod', [status(thm)], ['7', '8', '56'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]:
% 0.35/0.54         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.35/0.54         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.35/0.54         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.35/0.54  thf('62', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.35/0.54      inference('sup+', [status(thm)], ['61', '62'])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_B)
% 0.35/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['15', '16', '25'])).
% 0.35/0.54  thf('65', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.35/0.54      inference('sup+', [status(thm)], ['63', '64'])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '65', '66'])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54              (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= (~
% 0.35/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('split', [status(esa)], ['11'])).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.35/0.54         <= (~
% 0.35/0.54             (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.35/0.54  thf('71', plain,
% 0.35/0.54      (~
% 0.35/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.35/0.54             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['12', '53'])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.54         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.35/0.54  thf('73', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['67', '72'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
