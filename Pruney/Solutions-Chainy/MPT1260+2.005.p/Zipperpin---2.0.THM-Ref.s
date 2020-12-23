%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qIvn4SRtXM

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:22 EST 2020

% Result     : Theorem 15.78s
% Output     : Refutation 15.78s
% Verified   : 
% Statistics : Number of formulae       :  275 (1249 expanded)
%              Number of leaves         :   47 ( 413 expanded)
%              Depth                    :   22
%              Number of atoms          : 2504 (11511 expanded)
%              Number of equality atoms :  196 ( 879 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( v3_pre_topc @ X60 @ X61 )
      | ~ ( r1_tarski @ X60 @ X62 )
      | ( r1_tarski @ X60 @ ( k1_tops_1 @ X61 @ X62 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

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
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( ( k1_tops_1 @ X66 @ X65 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X66 ) @ X65 @ ( k2_tops_1 @ X66 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k2_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ ( k2_pre_topc @ X59 @ X58 ) @ ( k1_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X52 @ X53 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('80',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( r1_tarski @ X54 @ ( k2_pre_topc @ X55 @ X54 ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('86',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X42 @ X40 )
        = ( k9_subset_1 @ X41 @ X42 @ ( k3_subset_1 @ X41 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('95',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('97',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k9_subset_1 @ X30 @ X29 @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','93','98'])).

thf('100',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('107',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('109',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['106','113'])).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('116',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('128',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X1 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('132',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k7_subset_1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('136',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','138'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('140',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('141',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('142',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('145',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('152',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('155',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','153','158'])).

thf('160',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('163',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['161','168'])).

thf('170',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X42 @ X40 )
        = ( k9_subset_1 @ X41 @ X42 @ ( k3_subset_1 @ X41 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','153','158'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('176',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['174','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['171','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('184',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k9_subset_1 @ X39 @ X37 @ X38 )
        = ( k3_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','138'])).

thf('187',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['182','189','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ X1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['134','197'])).

thf('199',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k9_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['105','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('204',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('206',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['204','212'])).

thf('214',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('216',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('218',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X56 @ X57 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('219',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['216','222'])).

thf('224',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('225',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','72','73','225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qIvn4SRtXM
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 15.78/16.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.78/16.00  % Solved by: fo/fo7.sh
% 15.78/16.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.78/16.00  % done 23225 iterations in 15.510s
% 15.78/16.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.78/16.00  % SZS output start Refutation
% 15.78/16.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.78/16.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.78/16.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.78/16.00  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 15.78/16.00  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 15.78/16.00  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 15.78/16.00  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 15.78/16.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 15.78/16.00  thf(sk_B_type, type, sk_B: $i).
% 15.78/16.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.78/16.00  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 15.78/16.00  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 15.78/16.00  thf(sk_A_type, type, sk_A: $i).
% 15.78/16.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.78/16.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.78/16.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.78/16.00  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 15.78/16.00  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 15.78/16.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.78/16.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.78/16.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 15.78/16.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 15.78/16.00  thf(t76_tops_1, conjecture,
% 15.78/16.00    (![A:$i]:
% 15.78/16.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 15.78/16.00       ( ![B:$i]:
% 15.78/16.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00           ( ( v3_pre_topc @ B @ A ) <=>
% 15.78/16.00             ( ( k2_tops_1 @ A @ B ) =
% 15.78/16.00               ( k7_subset_1 @
% 15.78/16.00                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 15.78/16.00  thf(zf_stmt_0, negated_conjecture,
% 15.78/16.00    (~( ![A:$i]:
% 15.78/16.00        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 15.78/16.00          ( ![B:$i]:
% 15.78/16.00            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00              ( ( v3_pre_topc @ B @ A ) <=>
% 15.78/16.00                ( ( k2_tops_1 @ A @ B ) =
% 15.78/16.00                  ( k7_subset_1 @
% 15.78/16.00                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 15.78/16.00    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 15.78/16.00  thf('0', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 15.78/16.00        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('1', plain,
% 15.78/16.00      (~
% 15.78/16.00       (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 15.78/16.00       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('split', [status(esa)], ['0'])).
% 15.78/16.00  thf('2', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('3', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 15.78/16.00        | (v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('4', plain,
% 15.78/16.00      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('split', [status(esa)], ['3'])).
% 15.78/16.00  thf('5', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf(t56_tops_1, axiom,
% 15.78/16.00    (![A:$i]:
% 15.78/16.00     ( ( l1_pre_topc @ A ) =>
% 15.78/16.00       ( ![B:$i]:
% 15.78/16.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00           ( ![C:$i]:
% 15.78/16.00             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 15.78/16.00                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 15.78/16.00  thf('6', plain,
% 15.78/16.00      (![X60 : $i, X61 : $i, X62 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 15.78/16.00          | ~ (v3_pre_topc @ X60 @ X61)
% 15.78/16.00          | ~ (r1_tarski @ X60 @ X62)
% 15.78/16.00          | (r1_tarski @ X60 @ (k1_tops_1 @ X61 @ X62))
% 15.78/16.00          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 15.78/16.00          | ~ (l1_pre_topc @ X61))),
% 15.78/16.00      inference('cnf', [status(esa)], [t56_tops_1])).
% 15.78/16.00  thf('7', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         (~ (l1_pre_topc @ sk_A)
% 15.78/16.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.78/16.00          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 15.78/16.00          | ~ (r1_tarski @ sk_B @ X0)
% 15.78/16.00          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('sup-', [status(thm)], ['5', '6'])).
% 15.78/16.00  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('9', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.78/16.00          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 15.78/16.00          | ~ (r1_tarski @ sk_B @ X0)
% 15.78/16.00          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('demod', [status(thm)], ['7', '8'])).
% 15.78/16.00  thf('10', plain,
% 15.78/16.00      ((![X0 : $i]:
% 15.78/16.00          (~ (r1_tarski @ sk_B @ X0)
% 15.78/16.00           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 15.78/16.00           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 15.78/16.00         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['4', '9'])).
% 15.78/16.00  thf('11', plain,
% 15.78/16.00      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 15.78/16.00         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['2', '10'])).
% 15.78/16.00  thf(d10_xboole_0, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.78/16.00  thf('12', plain,
% 15.78/16.00      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 15.78/16.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.78/16.00  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 15.78/16.00      inference('simplify', [status(thm)], ['12'])).
% 15.78/16.00  thf('14', plain,
% 15.78/16.00      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 15.78/16.00         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('demod', [status(thm)], ['11', '13'])).
% 15.78/16.00  thf('15', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf(t3_subset, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 15.78/16.00  thf('16', plain,
% 15.78/16.00      (![X46 : $i, X47 : $i]:
% 15.78/16.00         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t3_subset])).
% 15.78/16.00  thf('17', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.78/16.00      inference('sup-', [status(thm)], ['15', '16'])).
% 15.78/16.00  thf(t28_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 15.78/16.00  thf('18', plain,
% 15.78/16.00      (![X12 : $i, X13 : $i]:
% 15.78/16.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 15.78/16.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.78/16.00  thf('19', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 15.78/16.00      inference('sup-', [status(thm)], ['17', '18'])).
% 15.78/16.00  thf(commutativity_k2_tarski, axiom,
% 15.78/16.00    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 15.78/16.00  thf('20', plain,
% 15.78/16.00      (![X23 : $i, X24 : $i]:
% 15.78/16.00         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 15.78/16.00      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 15.78/16.00  thf(t12_setfam_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.78/16.00  thf('21', plain,
% 15.78/16.00      (![X44 : $i, X45 : $i]:
% 15.78/16.00         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 15.78/16.00      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.78/16.00  thf('22', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['20', '21'])).
% 15.78/16.00  thf('23', plain,
% 15.78/16.00      (![X44 : $i, X45 : $i]:
% 15.78/16.00         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 15.78/16.00      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.78/16.00  thf('24', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf(t100_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.78/16.00  thf('25', plain,
% 15.78/16.00      (![X5 : $i, X6 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X5 @ X6)
% 15.78/16.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.78/16.00  thf('26', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X0 @ X1)
% 15.78/16.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.78/16.00      inference('sup+', [status(thm)], ['24', '25'])).
% 15.78/16.00  thf('27', plain,
% 15.78/16.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 15.78/16.00         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 15.78/16.00      inference('sup+', [status(thm)], ['19', '26'])).
% 15.78/16.00  thf(t48_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.78/16.00  thf('28', plain,
% 15.78/16.00      (![X21 : $i, X22 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 15.78/16.00           = (k3_xboole_0 @ X21 @ X22))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.78/16.00  thf('29', plain,
% 15.78/16.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 15.78/16.00         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 15.78/16.00      inference('sup+', [status(thm)], ['27', '28'])).
% 15.78/16.00  thf('30', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('31', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 15.78/16.00      inference('sup-', [status(thm)], ['17', '18'])).
% 15.78/16.00  thf('32', plain,
% 15.78/16.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 15.78/16.00      inference('demod', [status(thm)], ['29', '30', '31'])).
% 15.78/16.00  thf(t36_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 15.78/16.00  thf('33', plain,
% 15.78/16.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 15.78/16.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.78/16.00  thf('34', plain,
% 15.78/16.00      (![X46 : $i, X48 : $i]:
% 15.78/16.00         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 15.78/16.00      inference('cnf', [status(esa)], [t3_subset])).
% 15.78/16.00  thf('35', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['33', '34'])).
% 15.78/16.00  thf(t74_tops_1, axiom,
% 15.78/16.00    (![A:$i]:
% 15.78/16.00     ( ( l1_pre_topc @ A ) =>
% 15.78/16.00       ( ![B:$i]:
% 15.78/16.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00           ( ( k1_tops_1 @ A @ B ) =
% 15.78/16.00             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 15.78/16.00  thf('36', plain,
% 15.78/16.00      (![X65 : $i, X66 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 15.78/16.00          | ((k1_tops_1 @ X66 @ X65)
% 15.78/16.00              = (k7_subset_1 @ (u1_struct_0 @ X66) @ X65 @ 
% 15.78/16.00                 (k2_tops_1 @ X66 @ X65)))
% 15.78/16.00          | ~ (l1_pre_topc @ X66))),
% 15.78/16.00      inference('cnf', [status(esa)], [t74_tops_1])).
% 15.78/16.00  thf('37', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (~ (l1_pre_topc @ X0)
% 15.78/16.00          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 15.78/16.00              = (k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 15.78/16.00                 (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 15.78/16.00                 (k2_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['35', '36'])).
% 15.78/16.00  thf('38', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['33', '34'])).
% 15.78/16.00  thf(redefinition_k7_subset_1, axiom,
% 15.78/16.00    (![A:$i,B:$i,C:$i]:
% 15.78/16.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.78/16.00       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 15.78/16.00  thf('39', plain,
% 15.78/16.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 15.78/16.00          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 15.78/16.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 15.78/16.00  thf('40', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 15.78/16.00           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 15.78/16.00      inference('sup-', [status(thm)], ['38', '39'])).
% 15.78/16.00  thf('41', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (~ (l1_pre_topc @ X0)
% 15.78/16.00          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 15.78/16.00              = (k4_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 15.78/16.00                 (k2_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 15.78/16.00      inference('demod', [status(thm)], ['37', '40'])).
% 15.78/16.00  thf('42', plain,
% 15.78/16.00      ((((k1_tops_1 @ sk_A @ 
% 15.78/16.00          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00           (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 15.78/16.00          = (k4_xboole_0 @ sk_B @ 
% 15.78/16.00             (k2_tops_1 @ sk_A @ 
% 15.78/16.00              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00               (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 15.78/16.00        | ~ (l1_pre_topc @ sk_A))),
% 15.78/16.00      inference('sup+', [status(thm)], ['32', '41'])).
% 15.78/16.00  thf('43', plain,
% 15.78/16.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 15.78/16.00      inference('demod', [status(thm)], ['29', '30', '31'])).
% 15.78/16.00  thf('44', plain,
% 15.78/16.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 15.78/16.00      inference('demod', [status(thm)], ['29', '30', '31'])).
% 15.78/16.00  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('46', plain,
% 15.78/16.00      (((k1_tops_1 @ sk_A @ sk_B)
% 15.78/16.00         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 15.78/16.00      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 15.78/16.00  thf('47', plain,
% 15.78/16.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 15.78/16.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.78/16.00  thf('48', plain,
% 15.78/16.00      (![X2 : $i, X4 : $i]:
% 15.78/16.00         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 15.78/16.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.78/16.00  thf('49', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 15.78/16.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['47', '48'])).
% 15.78/16.00  thf('50', plain,
% 15.78/16.00      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 15.78/16.00        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['46', '49'])).
% 15.78/16.00  thf('51', plain,
% 15.78/16.00      (((k1_tops_1 @ sk_A @ sk_B)
% 15.78/16.00         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 15.78/16.00      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 15.78/16.00  thf('52', plain,
% 15.78/16.00      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 15.78/16.00        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 15.78/16.00      inference('demod', [status(thm)], ['50', '51'])).
% 15.78/16.00  thf('53', plain,
% 15.78/16.00      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 15.78/16.00         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['14', '52'])).
% 15.78/16.00  thf('54', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf(l78_tops_1, axiom,
% 15.78/16.00    (![A:$i]:
% 15.78/16.00     ( ( l1_pre_topc @ A ) =>
% 15.78/16.00       ( ![B:$i]:
% 15.78/16.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00           ( ( k2_tops_1 @ A @ B ) =
% 15.78/16.00             ( k7_subset_1 @
% 15.78/16.00               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 15.78/16.00               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 15.78/16.00  thf('55', plain,
% 15.78/16.00      (![X58 : $i, X59 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 15.78/16.00          | ((k2_tops_1 @ X59 @ X58)
% 15.78/16.00              = (k7_subset_1 @ (u1_struct_0 @ X59) @ 
% 15.78/16.00                 (k2_pre_topc @ X59 @ X58) @ (k1_tops_1 @ X59 @ X58)))
% 15.78/16.00          | ~ (l1_pre_topc @ X59))),
% 15.78/16.00      inference('cnf', [status(esa)], [l78_tops_1])).
% 15.78/16.00  thf('56', plain,
% 15.78/16.00      ((~ (l1_pre_topc @ sk_A)
% 15.78/16.00        | ((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['54', '55'])).
% 15.78/16.00  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('58', plain,
% 15.78/16.00      (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00            (k1_tops_1 @ sk_A @ sk_B)))),
% 15.78/16.00      inference('demod', [status(thm)], ['56', '57'])).
% 15.78/16.00  thf('59', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf(dt_k2_pre_topc, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( ( l1_pre_topc @ A ) & 
% 15.78/16.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.78/16.00       ( m1_subset_1 @
% 15.78/16.00         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 15.78/16.00  thf('60', plain,
% 15.78/16.00      (![X52 : $i, X53 : $i]:
% 15.78/16.00         (~ (l1_pre_topc @ X52)
% 15.78/16.00          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 15.78/16.00          | (m1_subset_1 @ (k2_pre_topc @ X52 @ X53) @ 
% 15.78/16.00             (k1_zfmisc_1 @ (u1_struct_0 @ X52))))),
% 15.78/16.00      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 15.78/16.00  thf('61', plain,
% 15.78/16.00      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.78/16.00        | ~ (l1_pre_topc @ sk_A))),
% 15.78/16.00      inference('sup-', [status(thm)], ['59', '60'])).
% 15.78/16.00  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('63', plain,
% 15.78/16.00      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('demod', [status(thm)], ['61', '62'])).
% 15.78/16.00  thf('64', plain,
% 15.78/16.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 15.78/16.00          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 15.78/16.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 15.78/16.00  thf('65', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['63', '64'])).
% 15.78/16.00  thf('66', plain,
% 15.78/16.00      (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00            (k1_tops_1 @ sk_A @ sk_B)))),
% 15.78/16.00      inference('demod', [status(thm)], ['58', '65'])).
% 15.78/16.00  thf('67', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('sup+', [status(thm)], ['53', '66'])).
% 15.78/16.00  thf('68', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['63', '64'])).
% 15.78/16.00  thf('69', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= (~
% 15.78/16.00             (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('split', [status(esa)], ['0'])).
% 15.78/16.00  thf('70', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= (~
% 15.78/16.00             (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['68', '69'])).
% 15.78/16.00  thf('71', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 15.78/16.00         <= (~
% 15.78/16.00             (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 15.78/16.00             ((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['67', '70'])).
% 15.78/16.00  thf('72', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 15.78/16.00       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('simplify', [status(thm)], ['71'])).
% 15.78/16.00  thf('73', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 15.78/16.00       ((v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('split', [status(esa)], ['3'])).
% 15.78/16.00  thf('74', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['63', '64'])).
% 15.78/16.00  thf('75', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('split', [status(esa)], ['3'])).
% 15.78/16.00  thf('76', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['74', '75'])).
% 15.78/16.00  thf('77', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['33', '34'])).
% 15.78/16.00  thf('78', plain,
% 15.78/16.00      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 15.78/16.00         (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B))))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['76', '77'])).
% 15.78/16.00  thf('79', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf(t48_pre_topc, axiom,
% 15.78/16.00    (![A:$i]:
% 15.78/16.00     ( ( l1_pre_topc @ A ) =>
% 15.78/16.00       ( ![B:$i]:
% 15.78/16.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.78/16.00           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 15.78/16.00  thf('80', plain,
% 15.78/16.00      (![X54 : $i, X55 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 15.78/16.00          | (r1_tarski @ X54 @ (k2_pre_topc @ X55 @ X54))
% 15.78/16.00          | ~ (l1_pre_topc @ X55))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_pre_topc])).
% 15.78/16.00  thf('81', plain,
% 15.78/16.00      ((~ (l1_pre_topc @ sk_A)
% 15.78/16.00        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['79', '80'])).
% 15.78/16.00  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('83', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 15.78/16.00      inference('demod', [status(thm)], ['81', '82'])).
% 15.78/16.00  thf('84', plain,
% 15.78/16.00      (![X46 : $i, X48 : $i]:
% 15.78/16.00         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 15.78/16.00      inference('cnf', [status(esa)], [t3_subset])).
% 15.78/16.00  thf('85', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['83', '84'])).
% 15.78/16.00  thf(t32_subset_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.78/16.00       ( ![C:$i]:
% 15.78/16.00         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.78/16.00           ( ( k7_subset_1 @ A @ B @ C ) =
% 15.78/16.00             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 15.78/16.00  thf('86', plain,
% 15.78/16.00      (![X40 : $i, X41 : $i, X42 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 15.78/16.00          | ((k7_subset_1 @ X41 @ X42 @ X40)
% 15.78/16.00              = (k9_subset_1 @ X41 @ X42 @ (k3_subset_1 @ X41 @ X40)))
% 15.78/16.00          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t32_subset_1])).
% 15.78/16.00  thf('87', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))
% 15.78/16.00          | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ sk_B)
% 15.78/16.00              = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ 
% 15.78/16.00                 (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['85', '86'])).
% 15.78/16.00  thf('88', plain,
% 15.78/16.00      ((((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00          (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 15.78/16.00          = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00             (k2_tops_1 @ sk_A @ sk_B) @ 
% 15.78/16.00             (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['78', '87'])).
% 15.78/16.00  thf('89', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 15.78/16.00      inference('sup-', [status(thm)], ['83', '84'])).
% 15.78/16.00  thf(d5_subset_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.78/16.00       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 15.78/16.00  thf('90', plain,
% 15.78/16.00      (![X25 : $i, X26 : $i]:
% 15.78/16.00         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 15.78/16.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 15.78/16.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 15.78/16.00  thf('91', plain,
% 15.78/16.00      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 15.78/16.00         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 15.78/16.00      inference('sup-', [status(thm)], ['89', '90'])).
% 15.78/16.00  thf('92', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['74', '75'])).
% 15.78/16.00  thf('93', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['91', '92'])).
% 15.78/16.00  thf('94', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 15.78/16.00      inference('simplify', [status(thm)], ['12'])).
% 15.78/16.00  thf('95', plain,
% 15.78/16.00      (![X46 : $i, X48 : $i]:
% 15.78/16.00         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 15.78/16.00      inference('cnf', [status(esa)], [t3_subset])).
% 15.78/16.00  thf('96', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['94', '95'])).
% 15.78/16.00  thf(idempotence_k9_subset_1, axiom,
% 15.78/16.00    (![A:$i,B:$i,C:$i]:
% 15.78/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.78/16.00       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 15.78/16.00  thf('97', plain,
% 15.78/16.00      (![X29 : $i, X30 : $i, X31 : $i]:
% 15.78/16.00         (((k9_subset_1 @ X30 @ X29 @ X29) = (X29))
% 15.78/16.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 15.78/16.00      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 15.78/16.00  thf('98', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 15.78/16.00      inference('sup-', [status(thm)], ['96', '97'])).
% 15.78/16.00  thf('99', plain,
% 15.78/16.00      ((((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00          (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('demod', [status(thm)], ['88', '93', '98'])).
% 15.78/16.00  thf('100', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['74', '75'])).
% 15.78/16.00  thf('101', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 15.78/16.00           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 15.78/16.00      inference('sup-', [status(thm)], ['38', '39'])).
% 15.78/16.00  thf('102', plain,
% 15.78/16.00      ((![X0 : $i]:
% 15.78/16.00          ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00            (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 15.78/16.00            = (k4_xboole_0 @ 
% 15.78/16.00               (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) @ X0)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['100', '101'])).
% 15.78/16.00  thf('103', plain,
% 15.78/16.00      ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['74', '75'])).
% 15.78/16.00  thf('104', plain,
% 15.78/16.00      ((![X0 : $i]:
% 15.78/16.00          ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.78/16.00            (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 15.78/16.00            = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('demod', [status(thm)], ['102', '103'])).
% 15.78/16.00  thf('105', plain,
% 15.78/16.00      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 15.78/16.00          = (k2_tops_1 @ sk_A @ sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('demod', [status(thm)], ['99', '104'])).
% 15.78/16.00  thf('106', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('107', plain,
% 15.78/16.00      (![X21 : $i, X22 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 15.78/16.00           = (k3_xboole_0 @ X21 @ X22))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.78/16.00  thf('108', plain,
% 15.78/16.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 15.78/16.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.78/16.00  thf(t12_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 15.78/16.00  thf('109', plain,
% 15.78/16.00      (![X7 : $i, X8 : $i]:
% 15.78/16.00         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 15.78/16.00      inference('cnf', [status(esa)], [t12_xboole_1])).
% 15.78/16.00  thf('110', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['108', '109'])).
% 15.78/16.00  thf(commutativity_k2_xboole_0, axiom,
% 15.78/16.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 15.78/16.00  thf('111', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.78/16.00  thf('112', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['110', '111'])).
% 15.78/16.00  thf('113', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['107', '112'])).
% 15.78/16.00  thf('114', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['106', '113'])).
% 15.78/16.00  thf('115', plain,
% 15.78/16.00      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 15.78/16.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.78/16.00  thf(t44_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i,C:$i]:
% 15.78/16.00     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 15.78/16.00       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.78/16.00  thf('116', plain,
% 15.78/16.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 15.78/16.00         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 15.78/16.00          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 15.78/16.00      inference('cnf', [status(esa)], [t44_xboole_1])).
% 15.78/16.00  thf('117', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['115', '116'])).
% 15.78/16.00  thf('118', plain,
% 15.78/16.00      (![X12 : $i, X13 : $i]:
% 15.78/16.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 15.78/16.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.78/16.00  thf('119', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['117', '118'])).
% 15.78/16.00  thf('120', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 15.78/16.00           = (k3_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['114', '119'])).
% 15.78/16.00  thf('121', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('122', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k3_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['120', '121'])).
% 15.78/16.00  thf('123', plain,
% 15.78/16.00      (![X5 : $i, X6 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X5 @ X6)
% 15.78/16.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.78/16.00  thf('124', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.78/16.00      inference('sup+', [status(thm)], ['122', '123'])).
% 15.78/16.00  thf('125', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X0 @ X1)
% 15.78/16.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.78/16.00      inference('sup+', [status(thm)], ['24', '25'])).
% 15.78/16.00  thf('126', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k4_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('demod', [status(thm)], ['124', '125'])).
% 15.78/16.00  thf('127', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['94', '95'])).
% 15.78/16.00  thf('128', plain,
% 15.78/16.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 15.78/16.00          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 15.78/16.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 15.78/16.00  thf('129', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup-', [status(thm)], ['127', '128'])).
% 15.78/16.00  thf('130', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X1 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 15.78/16.00           = (k4_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['126', '129'])).
% 15.78/16.00  thf('131', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup-', [status(thm)], ['127', '128'])).
% 15.78/16.00  thf('132', plain,
% 15.78/16.00      (![X21 : $i, X22 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 15.78/16.00           = (k3_xboole_0 @ X21 @ X22))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.78/16.00  thf('133', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X1 @ (k7_subset_1 @ X1 @ X1 @ X0))
% 15.78/16.00           = (k3_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['131', '132'])).
% 15.78/16.00  thf('134', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 15.78/16.00      inference('sup+', [status(thm)], ['130', '133'])).
% 15.78/16.00  thf('135', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('136', plain,
% 15.78/16.00      (![X21 : $i, X22 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 15.78/16.00           = (k3_xboole_0 @ X21 @ X22))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.78/16.00  thf('137', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['33', '34'])).
% 15.78/16.00  thf('138', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['136', '137'])).
% 15.78/16.00  thf('139', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['135', '138'])).
% 15.78/16.00  thf(t4_subset_1, axiom,
% 15.78/16.00    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 15.78/16.00  thf('140', plain,
% 15.78/16.00      (![X43 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 15.78/16.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.78/16.00  thf('141', plain,
% 15.78/16.00      (![X46 : $i, X47 : $i]:
% 15.78/16.00         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t3_subset])).
% 15.78/16.00  thf('142', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 15.78/16.00      inference('sup-', [status(thm)], ['140', '141'])).
% 15.78/16.00  thf('143', plain,
% 15.78/16.00      (![X7 : $i, X8 : $i]:
% 15.78/16.00         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 15.78/16.00      inference('cnf', [status(esa)], [t12_xboole_1])).
% 15.78/16.00  thf('144', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['142', '143'])).
% 15.78/16.00  thf(t39_xboole_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 15.78/16.00  thf('145', plain,
% 15.78/16.00      (![X16 : $i, X17 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 15.78/16.00           = (k2_xboole_0 @ X16 @ X17))),
% 15.78/16.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.78/16.00  thf('146', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['144', '145'])).
% 15.78/16.00  thf('147', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['142', '143'])).
% 15.78/16.00  thf('148', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['146', '147'])).
% 15.78/16.00  thf('149', plain,
% 15.78/16.00      (![X21 : $i, X22 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 15.78/16.00           = (k3_xboole_0 @ X21 @ X22))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.78/16.00  thf('150', plain,
% 15.78/16.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['148', '149'])).
% 15.78/16.00  thf('151', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['94', '95'])).
% 15.78/16.00  thf('152', plain,
% 15.78/16.00      (![X25 : $i, X26 : $i]:
% 15.78/16.00         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 15.78/16.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 15.78/16.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 15.78/16.00  thf('153', plain,
% 15.78/16.00      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['151', '152'])).
% 15.78/16.00  thf('154', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 15.78/16.00      inference('sup-', [status(thm)], ['140', '141'])).
% 15.78/16.00  thf('155', plain,
% 15.78/16.00      (![X12 : $i, X13 : $i]:
% 15.78/16.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 15.78/16.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.78/16.00  thf('156', plain,
% 15.78/16.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['154', '155'])).
% 15.78/16.00  thf('157', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('158', plain,
% 15.78/16.00      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['156', '157'])).
% 15.78/16.00  thf('159', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 15.78/16.00      inference('demod', [status(thm)], ['150', '153', '158'])).
% 15.78/16.00  thf('160', plain,
% 15.78/16.00      (![X43 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 15.78/16.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.78/16.00  thf('161', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['159', '160'])).
% 15.78/16.00  thf('162', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 15.78/16.00      inference('simplify', [status(thm)], ['12'])).
% 15.78/16.00  thf('163', plain,
% 15.78/16.00      (![X12 : $i, X13 : $i]:
% 15.78/16.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 15.78/16.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 15.78/16.00  thf('164', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['162', '163'])).
% 15.78/16.00  thf('165', plain,
% 15.78/16.00      (![X5 : $i, X6 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X5 @ X6)
% 15.78/16.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.78/16.00  thf('166', plain,
% 15.78/16.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['164', '165'])).
% 15.78/16.00  thf('167', plain,
% 15.78/16.00      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['151', '152'])).
% 15.78/16.00  thf('168', plain,
% 15.78/16.00      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['166', '167'])).
% 15.78/16.00  thf('169', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k5_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 15.78/16.00      inference('demod', [status(thm)], ['161', '168'])).
% 15.78/16.00  thf('170', plain,
% 15.78/16.00      (![X40 : $i, X41 : $i, X42 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 15.78/16.00          | ((k7_subset_1 @ X41 @ X42 @ X40)
% 15.78/16.00              = (k9_subset_1 @ X41 @ X42 @ (k3_subset_1 @ X41 @ X40)))
% 15.78/16.00          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 15.78/16.00      inference('cnf', [status(esa)], [t32_subset_1])).
% 15.78/16.00  thf('171', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 15.78/16.00          | ((k7_subset_1 @ X0 @ X2 @ (k5_xboole_0 @ X1 @ X1))
% 15.78/16.00              = (k9_subset_1 @ X0 @ X2 @ 
% 15.78/16.00                 (k3_subset_1 @ X0 @ (k5_xboole_0 @ X1 @ X1)))))),
% 15.78/16.00      inference('sup-', [status(thm)], ['169', '170'])).
% 15.78/16.00  thf('172', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 15.78/16.00      inference('demod', [status(thm)], ['150', '153', '158'])).
% 15.78/16.00  thf('173', plain,
% 15.78/16.00      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['166', '167'])).
% 15.78/16.00  thf('174', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.78/16.00      inference('demod', [status(thm)], ['172', '173'])).
% 15.78/16.00  thf('175', plain,
% 15.78/16.00      (![X43 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 15.78/16.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.78/16.00  thf('176', plain,
% 15.78/16.00      (![X25 : $i, X26 : $i]:
% 15.78/16.00         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 15.78/16.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 15.78/16.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 15.78/16.00  thf('177', plain,
% 15.78/16.00      (![X0 : $i]:
% 15.78/16.00         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['175', '176'])).
% 15.78/16.00  thf('178', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['146', '147'])).
% 15.78/16.00  thf('179', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['177', '178'])).
% 15.78/16.00  thf('180', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['174', '179'])).
% 15.78/16.00  thf('181', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 15.78/16.00          | ((k7_subset_1 @ X0 @ X2 @ (k5_xboole_0 @ X1 @ X1))
% 15.78/16.00              = (k9_subset_1 @ X0 @ X2 @ X0)))),
% 15.78/16.00      inference('demod', [status(thm)], ['171', '180'])).
% 15.78/16.00  thf('182', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X2))
% 15.78/16.00           = (k9_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['139', '181'])).
% 15.78/16.00  thf('183', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['94', '95'])).
% 15.78/16.00  thf(redefinition_k9_subset_1, axiom,
% 15.78/16.00    (![A:$i,B:$i,C:$i]:
% 15.78/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.78/16.00       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 15.78/16.00  thf('184', plain,
% 15.78/16.00      (![X37 : $i, X38 : $i, X39 : $i]:
% 15.78/16.00         (((k9_subset_1 @ X39 @ X37 @ X38) = (k3_xboole_0 @ X37 @ X38))
% 15.78/16.00          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 15.78/16.00      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 15.78/16.00  thf('185', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['183', '184'])).
% 15.78/16.00  thf('186', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['135', '138'])).
% 15.78/16.00  thf('187', plain,
% 15.78/16.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.78/16.00         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 15.78/16.00          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 15.78/16.00      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 15.78/16.00  thf('188', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 15.78/16.00           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 15.78/16.00      inference('sup-', [status(thm)], ['186', '187'])).
% 15.78/16.00  thf('189', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.78/16.00         ((k7_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 15.78/16.00           = (k4_xboole_0 @ (k9_subset_1 @ X0 @ X1 @ X0) @ X2))),
% 15.78/16.00      inference('sup+', [status(thm)], ['185', '188'])).
% 15.78/16.00  thf('190', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.78/16.00      inference('demod', [status(thm)], ['172', '173'])).
% 15.78/16.00  thf('191', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['146', '147'])).
% 15.78/16.00  thf('192', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['190', '191'])).
% 15.78/16.00  thf('193', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k9_subset_1 @ X0 @ X1 @ X0)
% 15.78/16.00           = (k9_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['182', '189', '192'])).
% 15.78/16.00  thf('194', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['183', '184'])).
% 15.78/16.00  thf('195', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('196', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_xboole_0 @ X0 @ X1) = (k9_subset_1 @ X0 @ X1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['194', '195'])).
% 15.78/16.00  thf('197', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['193', '196'])).
% 15.78/16.00  thf('198', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k9_subset_1 @ X1 @ X0 @ X1))),
% 15.78/16.00      inference('demod', [status(thm)], ['134', '197'])).
% 15.78/16.00  thf('199', plain,
% 15.78/16.00      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 15.78/16.00          = (k9_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 15.78/16.00             (k2_tops_1 @ sk_A @ sk_B))))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['105', '198'])).
% 15.78/16.00  thf('200', plain,
% 15.78/16.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['164', '165'])).
% 15.78/16.00  thf('201', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.78/16.00      inference('demod', [status(thm)], ['172', '173'])).
% 15.78/16.00  thf('202', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k3_xboole_0 @ X0 @ X1) = (k9_subset_1 @ X0 @ X1 @ X0))),
% 15.78/16.00      inference('sup+', [status(thm)], ['194', '195'])).
% 15.78/16.00  thf('203', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['22', '23'])).
% 15.78/16.00  thf('204', plain,
% 15.78/16.00      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 15.78/16.00  thf('205', plain,
% 15.78/16.00      (![X21 : $i, X22 : $i]:
% 15.78/16.00         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 15.78/16.00           = (k3_xboole_0 @ X21 @ X22))),
% 15.78/16.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.78/16.00  thf('206', plain,
% 15.78/16.00      (![X16 : $i, X17 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 15.78/16.00           = (k2_xboole_0 @ X16 @ X17))),
% 15.78/16.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.78/16.00  thf('207', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 15.78/16.00      inference('sup+', [status(thm)], ['205', '206'])).
% 15.78/16.00  thf('208', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.78/16.00  thf('209', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.78/16.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.78/16.00  thf('210', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.78/16.00      inference('demod', [status(thm)], ['207', '208', '209'])).
% 15.78/16.00  thf('211', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 15.78/16.00      inference('demod', [status(thm)], ['110', '111'])).
% 15.78/16.00  thf('212', plain,
% 15.78/16.00      (![X0 : $i, X1 : $i]:
% 15.78/16.00         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.78/16.00           = (X1))),
% 15.78/16.00      inference('demod', [status(thm)], ['210', '211'])).
% 15.78/16.00  thf('213', plain,
% 15.78/16.00      ((((k2_xboole_0 @ k1_xboole_0 @ 
% 15.78/16.00          (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['204', '212'])).
% 15.78/16.00  thf('214', plain,
% 15.78/16.00      (((k1_tops_1 @ sk_A @ sk_B)
% 15.78/16.00         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 15.78/16.00      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 15.78/16.00  thf('215', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.78/16.00      inference('sup-', [status(thm)], ['142', '143'])).
% 15.78/16.00  thf('216', plain,
% 15.78/16.00      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('demod', [status(thm)], ['213', '214', '215'])).
% 15.78/16.00  thf('217', plain,
% 15.78/16.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf(fc9_tops_1, axiom,
% 15.78/16.00    (![A:$i,B:$i]:
% 15.78/16.00     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 15.78/16.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.78/16.00       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 15.78/16.00  thf('218', plain,
% 15.78/16.00      (![X56 : $i, X57 : $i]:
% 15.78/16.00         (~ (l1_pre_topc @ X56)
% 15.78/16.00          | ~ (v2_pre_topc @ X56)
% 15.78/16.00          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 15.78/16.00          | (v3_pre_topc @ (k1_tops_1 @ X56 @ X57) @ X56))),
% 15.78/16.00      inference('cnf', [status(esa)], [fc9_tops_1])).
% 15.78/16.00  thf('219', plain,
% 15.78/16.00      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 15.78/16.00        | ~ (v2_pre_topc @ sk_A)
% 15.78/16.00        | ~ (l1_pre_topc @ sk_A))),
% 15.78/16.00      inference('sup-', [status(thm)], ['217', '218'])).
% 15.78/16.00  thf('220', plain, ((v2_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('221', plain, ((l1_pre_topc @ sk_A)),
% 15.78/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.78/16.00  thf('222', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 15.78/16.00      inference('demod', [status(thm)], ['219', '220', '221'])).
% 15.78/16.00  thf('223', plain,
% 15.78/16.00      (((v3_pre_topc @ sk_B @ sk_A))
% 15.78/16.00         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 15.78/16.00      inference('sup+', [status(thm)], ['216', '222'])).
% 15.78/16.00  thf('224', plain,
% 15.78/16.00      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 15.78/16.00      inference('split', [status(esa)], ['0'])).
% 15.78/16.00  thf('225', plain,
% 15.78/16.00      (~
% 15.78/16.00       (((k2_tops_1 @ sk_A @ sk_B)
% 15.78/16.00          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 15.78/16.00             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 15.78/16.00       ((v3_pre_topc @ sk_B @ sk_A))),
% 15.78/16.00      inference('sup-', [status(thm)], ['223', '224'])).
% 15.78/16.00  thf('226', plain, ($false),
% 15.78/16.00      inference('sat_resolution*', [status(thm)], ['1', '72', '73', '225'])).
% 15.78/16.00  
% 15.78/16.00  % SZS output end Refutation
% 15.78/16.00  
% 15.78/16.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
