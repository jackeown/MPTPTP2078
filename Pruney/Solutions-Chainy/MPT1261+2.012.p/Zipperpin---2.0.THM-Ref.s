%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yCvlXvU4fK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:38 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 360 expanded)
%              Number of leaves         :   43 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          : 1652 (4280 expanded)
%              Number of equality atoms :  130 ( 262 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( v4_pre_topc @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k1_tops_1 @ X46 @ X45 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

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
    inference('sup-',[status(thm)],['21','22'])).

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

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k9_subset_1 @ X29 @ X27 @ X28 )
        = ( k3_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('64',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('68',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('75',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('77',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('81',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('83',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','99'])).

thf('101',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','100'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('103',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('104',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('105',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('110',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','118'])).

thf('120',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','119'])).

thf('121',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('123',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
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

thf('129',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_pre_topc @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
       != X39 )
      | ( v4_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('137',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yCvlXvU4fK
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 805 iterations in 0.254s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.52/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.52/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.52/0.71  thf(t77_tops_1, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.52/0.71             ( ( k2_tops_1 @ A @ B ) =
% 0.52/0.71               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71          ( ![B:$i]:
% 0.52/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71              ( ( v4_pre_topc @ B @ A ) <=>
% 0.52/0.71                ( ( k2_tops_1 @ A @ B ) =
% 0.52/0.71                  ( k7_subset_1 @
% 0.52/0.71                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71              (k1_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      (~
% 0.52/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.52/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71             (k1_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('split', [status(esa)], ['2'])).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t69_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( v4_pre_topc @ B @ A ) =>
% 0.52/0.71             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X43 : $i, X44 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.52/0.71          | (r1_tarski @ (k2_tops_1 @ X44 @ X43) @ X43)
% 0.52/0.71          | ~ (v4_pre_topc @ X43 @ X44)
% 0.52/0.71          | ~ (l1_pre_topc @ X44))),
% 0.52/0.71      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.52/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.71  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.52/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['3', '8'])).
% 0.52/0.71  thf(t3_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X33 : $i, X35 : $i]:
% 0.52/0.71         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.71  thf(involutiveness_k3_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X19 : $i, X20 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.52/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.52/0.71      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.71  thf(d5_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.52/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.71          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t74_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( k1_tops_1 @ A @ B ) =
% 0.52/0.71             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X45 : $i, X46 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.52/0.71          | ((k1_tops_1 @ X46 @ X45)
% 0.52/0.71              = (k7_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.52/0.71                 (k2_tops_1 @ X46 @ X45)))
% 0.52/0.71          | ~ (l1_pre_topc @ X46))),
% 0.52/0.71      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.52/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.52/0.71          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.52/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.52/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['16', '24'])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.52/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['13', '25'])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.52/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.52/0.71  thf(t36_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.52/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X33 : $i, X35 : $i]:
% 0.52/0.71         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['27', '30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i]:
% 0.52/0.71         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.52/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.52/0.71         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.52/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71              (k1_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= (~
% 0.52/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= (~
% 0.52/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= (~
% 0.52/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['33', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (~
% 0.52/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.52/0.71             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['26', '37'])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.52/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('simplify', [status(thm)], ['38'])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.52/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('split', [status(esa)], ['2'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.52/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.71      inference('split', [status(esa)], ['2'])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.52/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.52/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.52/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['43', '44'])).
% 0.52/0.72  thf(t28_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.72  thf('47', plain,
% 0.52/0.72      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.52/0.72          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.72  thf('48', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(dt_k9_subset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.72       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.72         ((m1_subset_1 @ (k9_subset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X16))
% 0.52/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X16)))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.52/0.72  thf('50', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.72  thf('51', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(redefinition_k9_subset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.72       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.72         (((k9_subset_1 @ X29 @ X27 @ X28) = (k3_xboole_0 @ X27 @ X28))
% 0.52/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.72  thf('53', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.52/0.72           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.72  thf('54', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['50', '53'])).
% 0.52/0.72  thf('55', plain,
% 0.52/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['47', '54'])).
% 0.52/0.72  thf('56', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(redefinition_k4_subset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.52/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.52/0.72  thf('57', plain,
% 0.52/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.52/0.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.52/0.72          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.52/0.72  thf('58', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.52/0.72            = (k2_xboole_0 @ sk_B @ X0))
% 0.52/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.72  thf('59', plain,
% 0.52/0.72      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.72          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['55', '58'])).
% 0.52/0.72  thf('60', plain,
% 0.52/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['41', '42'])).
% 0.52/0.72  thf('61', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.72  thf('62', plain,
% 0.52/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['60', '61'])).
% 0.52/0.72  thf('63', plain,
% 0.52/0.72      (![X19 : $i, X20 : $i]:
% 0.52/0.72         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.52/0.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.52/0.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.52/0.72  thf('64', plain,
% 0.52/0.72      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.72  thf('65', plain,
% 0.52/0.72      (((k1_tops_1 @ sk_A @ sk_B)
% 0.52/0.72         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.52/0.72  thf('66', plain,
% 0.52/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['60', '61'])).
% 0.52/0.72  thf('67', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i]:
% 0.52/0.72         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.52/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.72  thf('68', plain,
% 0.52/0.72      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.72          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.72  thf('69', plain,
% 0.52/0.72      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.72          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['65', '68'])).
% 0.52/0.72  thf('70', plain,
% 0.52/0.72      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.52/0.72          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('demod', [status(thm)], ['64', '69'])).
% 0.52/0.72  thf('71', plain,
% 0.52/0.72      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.52/0.72         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.72  thf('72', plain,
% 0.52/0.72      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.52/0.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.72  thf('73', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.72  thf('74', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.52/0.72           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['72', '73'])).
% 0.52/0.72  thf(t100_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.72  thf('75', plain,
% 0.52/0.72      (![X3 : $i, X4 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.72           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.72  thf('76', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.72           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['74', '75'])).
% 0.52/0.72  thf(t4_subset_1, axiom,
% 0.52/0.72    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.72  thf('77', plain,
% 0.52/0.72      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.72  thf('78', plain,
% 0.52/0.72      (![X19 : $i, X20 : $i]:
% 0.52/0.72         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.52/0.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.52/0.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.52/0.72  thf('79', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['77', '78'])).
% 0.52/0.72  thf('80', plain,
% 0.52/0.72      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.72  thf('81', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i]:
% 0.52/0.72         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.52/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.72  thf('82', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.52/0.72  thf(t3_boole, axiom,
% 0.52/0.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.72  thf('83', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.72  thf('84', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['82', '83'])).
% 0.52/0.72  thf('85', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['79', '84'])).
% 0.52/0.72  thf('86', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.72  thf('87', plain,
% 0.52/0.72      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.52/0.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.72  thf('88', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.52/0.72      inference('sup+', [status(thm)], ['86', '87'])).
% 0.52/0.72  thf('89', plain,
% 0.52/0.72      (![X33 : $i, X35 : $i]:
% 0.52/0.72         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('90', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['88', '89'])).
% 0.52/0.72  thf('91', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i]:
% 0.52/0.72         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.52/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.72  thf('92', plain,
% 0.52/0.72      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['90', '91'])).
% 0.52/0.72  thf('93', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.52/0.72      inference('sup+', [status(thm)], ['86', '87'])).
% 0.52/0.72  thf('94', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.72  thf('95', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['93', '94'])).
% 0.52/0.72  thf('96', plain,
% 0.52/0.72      (![X3 : $i, X4 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.72           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.72  thf('97', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['95', '96'])).
% 0.52/0.72  thf('98', plain,
% 0.52/0.72      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['92', '97'])).
% 0.52/0.72  thf('99', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['85', '98'])).
% 0.52/0.72  thf('100', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['76', '99'])).
% 0.52/0.72  thf('101', plain,
% 0.52/0.72      (((k4_xboole_0 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 0.52/0.72         = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['71', '100'])).
% 0.52/0.72  thf(t98_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.52/0.72  thf('102', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X10 @ X11)
% 0.52/0.72           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.52/0.72  thf('103', plain,
% 0.52/0.72      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['101', '102'])).
% 0.52/0.72  thf(commutativity_k2_tarski, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.52/0.72  thf('104', plain,
% 0.52/0.72      (![X12 : $i, X13 : $i]:
% 0.52/0.72         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.52/0.72  thf(t12_setfam_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.72  thf('105', plain,
% 0.52/0.72      (![X31 : $i, X32 : $i]:
% 0.52/0.72         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.52/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.52/0.72  thf('106', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['104', '105'])).
% 0.52/0.72  thf('107', plain,
% 0.52/0.72      (![X31 : $i, X32 : $i]:
% 0.52/0.72         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.52/0.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.52/0.72  thf('108', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['106', '107'])).
% 0.52/0.72  thf('109', plain,
% 0.52/0.72      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.72  thf('110', plain,
% 0.52/0.72      (![X33 : $i, X34 : $i]:
% 0.52/0.72         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('111', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['109', '110'])).
% 0.52/0.72  thf('112', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.72  thf('113', plain,
% 0.52/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['111', '112'])).
% 0.52/0.72  thf('114', plain,
% 0.52/0.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['108', '113'])).
% 0.52/0.72  thf('115', plain,
% 0.52/0.72      (![X3 : $i, X4 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.72           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.72  thf('116', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['114', '115'])).
% 0.52/0.72  thf('117', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.72  thf('118', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['116', '117'])).
% 0.52/0.72  thf('119', plain,
% 0.52/0.72      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.52/0.72         = (sk_B))),
% 0.52/0.72      inference('demod', [status(thm)], ['103', '118'])).
% 0.52/0.72  thf('120', plain,
% 0.52/0.72      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['70', '119'])).
% 0.52/0.72  thf('121', plain,
% 0.52/0.72      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.72          = (sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('demod', [status(thm)], ['59', '120'])).
% 0.52/0.72  thf('122', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(t65_tops_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( l1_pre_topc @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( k2_pre_topc @ A @ B ) =
% 0.52/0.72             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.72  thf('123', plain,
% 0.52/0.72      (![X41 : $i, X42 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.52/0.72          | ((k2_pre_topc @ X42 @ X41)
% 0.52/0.72              = (k4_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 0.52/0.72                 (k2_tops_1 @ X42 @ X41)))
% 0.52/0.72          | ~ (l1_pre_topc @ X42))),
% 0.52/0.72      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.52/0.72  thf('124', plain,
% 0.52/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.72        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.52/0.72            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['122', '123'])).
% 0.52/0.72  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('126', plain,
% 0.52/0.72      (((k2_pre_topc @ sk_A @ sk_B)
% 0.52/0.72         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['124', '125'])).
% 0.52/0.72  thf('127', plain,
% 0.52/0.72      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['121', '126'])).
% 0.52/0.72  thf('128', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(t52_pre_topc, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( l1_pre_topc @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.52/0.72             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.52/0.72               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.52/0.72  thf('129', plain,
% 0.52/0.72      (![X39 : $i, X40 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.52/0.72          | ~ (v2_pre_topc @ X40)
% 0.52/0.72          | ((k2_pre_topc @ X40 @ X39) != (X39))
% 0.52/0.72          | (v4_pre_topc @ X39 @ X40)
% 0.52/0.72          | ~ (l1_pre_topc @ X40))),
% 0.52/0.72      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.52/0.72  thf('130', plain,
% 0.52/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.72        | (v4_pre_topc @ sk_B @ sk_A)
% 0.52/0.72        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.52/0.72        | ~ (v2_pre_topc @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['128', '129'])).
% 0.52/0.72  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('133', plain,
% 0.52/0.72      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.52/0.72  thf('134', plain,
% 0.52/0.72      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['127', '133'])).
% 0.52/0.72  thf('135', plain,
% 0.52/0.72      (((v4_pre_topc @ sk_B @ sk_A))
% 0.52/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.52/0.72      inference('simplify', [status(thm)], ['134'])).
% 0.52/0.72  thf('136', plain,
% 0.52/0.72      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('137', plain,
% 0.52/0.72      (~
% 0.52/0.72       (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.52/0.72       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['135', '136'])).
% 0.52/0.72  thf('138', plain, ($false),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '137'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
