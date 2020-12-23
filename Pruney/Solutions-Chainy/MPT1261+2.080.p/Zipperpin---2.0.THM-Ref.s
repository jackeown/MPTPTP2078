%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MtyvH7wnDZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:49 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 152 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  898 (1965 expanded)
%              Number of equality atoms :   68 ( 119 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

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
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_pre_topc @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
       != X20 )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MtyvH7wnDZ
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 152 iterations in 0.106s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.41/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.41/0.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.41/0.58  thf(t77_tops_1, conjecture,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.41/0.58             ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.58               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i]:
% 0.41/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.58          ( ![B:$i]:
% 0.41/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.58              ( ( v4_pre_topc @ B @ A ) <=>
% 0.41/0.58                ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.58                  ( k7_subset_1 @
% 0.41/0.58                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58              (k1_tops_1 @ sk_A @ sk_B)))
% 0.41/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (~
% 0.41/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.41/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B)))
% 0.41/0.58        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t52_pre_topc, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.41/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.41/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X20 : $i, X21 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.58          | ~ (v4_pre_topc @ X20 @ X21)
% 0.41/0.58          | ((k2_pre_topc @ X21 @ X20) = (X20))
% 0.41/0.58          | ~ (l1_pre_topc @ X21))),
% 0.41/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.58        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.41/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.41/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['3', '8'])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(l78_tops_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.58           ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.58             ( k7_subset_1 @
% 0.41/0.58               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.41/0.58               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      (![X24 : $i, X25 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.58          | ((k2_tops_1 @ X25 @ X24)
% 0.41/0.58              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.41/0.58                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 0.41/0.58          | ~ (l1_pre_topc @ X25))),
% 0.41/0.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['9', '14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.58          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['15', '18'])).
% 0.41/0.58  thf('20', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58              (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.58         <= (~
% 0.41/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.58         <= (~
% 0.41/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.58         <= (~
% 0.41/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.41/0.58             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.41/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.41/0.58       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(dt_k2_tops_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.58       ( m1_subset_1 @
% 0.41/0.58         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      (![X22 : $i, X23 : $i]:
% 0.41/0.58         (~ (l1_pre_topc @ X22)
% 0.41/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.58          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 0.41/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.41/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.58  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.41/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.58  thf('32', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.41/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.41/0.58          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.41/0.58  thf('33', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.41/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.58         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t65_tops_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.58           ( ( k2_pre_topc @ A @ B ) =
% 0.41/0.58             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X26 : $i, X27 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.58          | ((k2_pre_topc @ X27 @ X26)
% 0.41/0.58              = (k4_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.41/0.58                 (k2_tops_1 @ X27 @ X26)))
% 0.41/0.58          | ~ (l1_pre_topc @ X27))),
% 0.41/0.58      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.58        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.58            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.58  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.58         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['34', '39'])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('42', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.41/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.58  thf(t36_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.41/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.41/0.58  thf(t28_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.58  thf('45', plain,
% 0.41/0.58      (![X4 : $i, X5 : $i]:
% 0.41/0.58         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.41/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.41/0.58           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.58  thf(commutativity_k2_tarski, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.58  thf('47', plain,
% 0.41/0.58      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.58  thf(t12_setfam_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.58  thf('48', plain,
% 0.41/0.58      (![X18 : $i, X19 : $i]:
% 0.41/0.58         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.41/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.41/0.58  thf('49', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.41/0.58  thf('50', plain,
% 0.41/0.58      (![X18 : $i, X19 : $i]:
% 0.41/0.58         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.41/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.41/0.58  thf('51', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['49', '50'])).
% 0.41/0.58  thf('52', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.41/0.58           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('demod', [status(thm)], ['46', '51'])).
% 0.41/0.58  thf(t22_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.41/0.58  thf('53', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.41/0.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.41/0.58  thf('54', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['52', '53'])).
% 0.41/0.58  thf('55', plain,
% 0.41/0.58      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.41/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('sup+', [status(thm)], ['43', '54'])).
% 0.41/0.58  thf('56', plain,
% 0.41/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.41/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('sup+', [status(thm)], ['40', '55'])).
% 0.41/0.58  thf('57', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('58', plain,
% 0.41/0.58      (![X20 : $i, X21 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.41/0.58          | ~ (v2_pre_topc @ X21)
% 0.41/0.58          | ((k2_pre_topc @ X21 @ X20) != (X20))
% 0.41/0.58          | (v4_pre_topc @ X20 @ X21)
% 0.41/0.58          | ~ (l1_pre_topc @ X21))),
% 0.41/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.41/0.58  thf('59', plain,
% 0.41/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.58        | (v4_pre_topc @ sk_B @ sk_A)
% 0.41/0.58        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.41/0.58        | ~ (v2_pre_topc @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.58  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('62', plain,
% 0.41/0.58      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.41/0.58  thf('63', plain,
% 0.41/0.58      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.41/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['56', '62'])).
% 0.41/0.58  thf('64', plain,
% 0.41/0.58      (((v4_pre_topc @ sk_B @ sk_A))
% 0.41/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.41/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.41/0.58  thf('65', plain,
% 0.41/0.58      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('66', plain,
% 0.41/0.58      (~
% 0.41/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.41/0.58       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.58  thf('67', plain, ($false),
% 0.41/0.58      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '66'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
