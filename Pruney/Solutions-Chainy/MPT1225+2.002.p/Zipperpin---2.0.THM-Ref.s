%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3q5TTSnoxq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:46 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 335 expanded)
%              Number of leaves         :   26 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  960 (5844 expanded)
%              Number of equality atoms :   52 ( 250 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t34_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X20 @ X18 )
        = ( k9_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','8','11'])).

thf('13',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ X23 @ ( k2_pre_topc @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['13','22'])).

thf('33',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['43','49'])).

thf('51',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('52',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('53',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('56',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X26 @ ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X27 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k2_pre_topc @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','67','68','69'])).

thf('71',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('75',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['57','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3q5TTSnoxq
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.66/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.87  % Solved by: fo/fo7.sh
% 0.66/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.87  % done 475 iterations in 0.419s
% 0.66/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.87  % SZS output start Refutation
% 0.66/0.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.66/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.87  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.66/0.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.87  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.66/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.87  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.66/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.87  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.66/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.87  thf(t34_tops_1, conjecture,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( ![C:$i]:
% 0.66/0.87             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.66/0.87                 ( ( k2_pre_topc @
% 0.66/0.87                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.66/0.87                   ( k9_subset_1 @
% 0.66/0.87                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.66/0.87                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.66/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.87    (~( ![A:$i]:
% 0.66/0.87        ( ( l1_pre_topc @ A ) =>
% 0.66/0.87          ( ![B:$i]:
% 0.66/0.87            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87              ( ![C:$i]:
% 0.66/0.87                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.66/0.87                    ( ( k2_pre_topc @
% 0.66/0.87                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.66/0.87                      ( k9_subset_1 @
% 0.66/0.87                        ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.66/0.87                        ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.66/0.87    inference('cnf.neg', [status(esa)], [t34_tops_1])).
% 0.66/0.87  thf('0', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('1', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(dt_k3_subset_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.66/0.87  thf('2', plain,
% 0.66/0.87      (![X8 : $i, X9 : $i]:
% 0.66/0.87         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.66/0.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.66/0.87      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.66/0.87  thf('3', plain,
% 0.66/0.87      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.87  thf(t32_subset_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87       ( ![C:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.66/0.87             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.66/0.87  thf('4', plain,
% 0.66/0.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.66/0.87          | ((k7_subset_1 @ X19 @ X20 @ X18)
% 0.66/0.87              = (k9_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X18)))
% 0.66/0.87          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.66/0.87      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.66/0.87  thf('5', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.87          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.87              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.87              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.87                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.87                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.87      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.87  thf('6', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(involutiveness_k3_subset_1, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.66/0.87  thf('7', plain,
% 0.66/0.87      (![X13 : $i, X14 : $i]:
% 0.66/0.87         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.66/0.87          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.66/0.87      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.66/0.87  thf('8', plain,
% 0.66/0.87      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.87         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['6', '7'])).
% 0.66/0.87  thf('9', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(redefinition_k9_subset_1, axiom,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.66/0.87  thf('10', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.87         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 0.66/0.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.66/0.87      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.66/0.87  thf('11', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.66/0.87           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.87  thf('12', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.87          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.66/0.87              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.87              = (k3_xboole_0 @ X0 @ sk_B)))),
% 0.66/0.87      inference('demod', [status(thm)], ['5', '8', '11'])).
% 0.66/0.87  thf('13', plain,
% 0.66/0.87      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.66/0.87         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.87         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['0', '12'])).
% 0.66/0.87  thf('14', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.66/0.87           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.87  thf('15', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(commutativity_k9_subset_1, axiom,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.66/0.87  thf('16', plain,
% 0.66/0.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.66/0.87         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.66/0.87          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.66/0.87  thf('17', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.66/0.87           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.66/0.87      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.87  thf('18', plain,
% 0.66/0.87      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.66/0.87         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('sup+', [status(thm)], ['14', '17'])).
% 0.66/0.87  thf('19', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('20', plain,
% 0.66/0.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.66/0.87         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 0.66/0.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.66/0.87      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.66/0.87  thf('21', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.66/0.87           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.66/0.87      inference('sup-', [status(thm)], ['19', '20'])).
% 0.66/0.87  thf('22', plain,
% 0.66/0.87      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['18', '21'])).
% 0.66/0.87  thf('23', plain,
% 0.66/0.87      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.66/0.87         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.87         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['13', '22'])).
% 0.66/0.87  thf('24', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(dt_k7_subset_1, axiom,
% 0.66/0.87    (![A:$i,B:$i,C:$i]:
% 0.66/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.87       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.66/0.87  thf('25', plain,
% 0.66/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.66/0.87          | (m1_subset_1 @ (k7_subset_1 @ X11 @ X10 @ X12) @ 
% 0.66/0.87             (k1_zfmisc_1 @ X11)))),
% 0.66/0.87      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.66/0.87  thf('26', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.66/0.87          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('sup-', [status(thm)], ['24', '25'])).
% 0.66/0.87  thf(t48_pre_topc, axiom,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.66/0.87  thf('27', plain,
% 0.66/0.87      (![X23 : $i, X24 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.66/0.87          | (r1_tarski @ X23 @ (k2_pre_topc @ X24 @ X23))
% 0.66/0.87          | ~ (l1_pre_topc @ X24))),
% 0.66/0.87      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.66/0.87  thf('28', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (l1_pre_topc @ sk_A)
% 0.66/0.87          | (r1_tarski @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.66/0.87             (k2_pre_topc @ sk_A @ 
% 0.66/0.87              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 0.66/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.87  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('30', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (r1_tarski @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.66/0.87          (k2_pre_topc @ sk_A @ 
% 0.66/0.87           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))),
% 0.66/0.87      inference('demod', [status(thm)], ['28', '29'])).
% 0.66/0.87  thf('31', plain,
% 0.66/0.87      ((r1_tarski @ 
% 0.66/0.87        (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.66/0.87         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.66/0.87        (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.66/0.87      inference('sup+', [status(thm)], ['23', '30'])).
% 0.66/0.87  thf('32', plain,
% 0.66/0.87      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.66/0.87         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.87         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['13', '22'])).
% 0.66/0.87  thf('33', plain,
% 0.66/0.87      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.66/0.87        (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.66/0.87      inference('demod', [status(thm)], ['31', '32'])).
% 0.66/0.87  thf(d10_xboole_0, axiom,
% 0.66/0.87    (![A:$i,B:$i]:
% 0.66/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.87  thf('34', plain,
% 0.66/0.87      (![X0 : $i, X2 : $i]:
% 0.66/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.66/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.87  thf('35', plain,
% 0.66/0.87      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.66/0.87           (k3_xboole_0 @ sk_B @ sk_C))
% 0.66/0.87        | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.66/0.87            = (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.66/0.87      inference('sup-', [status(thm)], ['33', '34'])).
% 0.66/0.87  thf('36', plain,
% 0.66/0.87      (((k2_pre_topc @ sk_A @ 
% 0.66/0.87         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.66/0.87         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.87             (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('37', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(t52_pre_topc, axiom,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.66/0.87             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.66/0.87               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.66/0.87  thf('38', plain,
% 0.66/0.87      (![X28 : $i, X29 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.66/0.87          | ~ (v4_pre_topc @ X28 @ X29)
% 0.66/0.87          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.66/0.87          | ~ (l1_pre_topc @ X29))),
% 0.66/0.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.66/0.87  thf('39', plain,
% 0.66/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.87        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.66/0.87        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.66/0.87      inference('sup-', [status(thm)], ['37', '38'])).
% 0.66/0.87  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('41', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('42', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.66/0.87  thf('43', plain,
% 0.66/0.87      (((k2_pre_topc @ sk_A @ 
% 0.66/0.87         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.66/0.87         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.87             (k2_pre_topc @ sk_A @ sk_C)))),
% 0.66/0.87      inference('demod', [status(thm)], ['36', '42'])).
% 0.66/0.87  thf('44', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('45', plain,
% 0.66/0.87      (![X28 : $i, X29 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.66/0.87          | ~ (v4_pre_topc @ X28 @ X29)
% 0.66/0.87          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.66/0.87          | ~ (l1_pre_topc @ X29))),
% 0.66/0.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.66/0.87  thf('46', plain,
% 0.66/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.87        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.66/0.87        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.66/0.87      inference('sup-', [status(thm)], ['44', '45'])).
% 0.66/0.87  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('48', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('49', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.66/0.87  thf('50', plain,
% 0.66/0.87      (((k2_pre_topc @ sk_A @ 
% 0.66/0.87         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.66/0.87         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['43', '49'])).
% 0.66/0.87  thf('51', plain,
% 0.66/0.87      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.66/0.87         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('sup+', [status(thm)], ['14', '17'])).
% 0.66/0.87  thf('52', plain,
% 0.66/0.87      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.66/0.87         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('sup+', [status(thm)], ['14', '17'])).
% 0.66/0.87  thf('53', plain,
% 0.66/0.87      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))
% 0.66/0.87         != (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.66/0.87  thf('54', plain,
% 0.66/0.87      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['18', '21'])).
% 0.66/0.87  thf('55', plain,
% 0.66/0.87      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['18', '21'])).
% 0.66/0.87  thf('56', plain,
% 0.66/0.87      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.66/0.87         != (k3_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.66/0.87  thf('57', plain,
% 0.66/0.87      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.66/0.87          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.87      inference('simplify_reflect-', [status(thm)], ['35', '56'])).
% 0.66/0.87  thf('58', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('59', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf(t51_pre_topc, axiom,
% 0.66/0.87    (![A:$i]:
% 0.66/0.87     ( ( l1_pre_topc @ A ) =>
% 0.66/0.87       ( ![B:$i]:
% 0.66/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87           ( ![C:$i]:
% 0.66/0.87             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.87               ( r1_tarski @
% 0.66/0.87                 ( k2_pre_topc @
% 0.66/0.87                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 0.66/0.87                 ( k9_subset_1 @
% 0.66/0.87                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.66/0.87                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.66/0.87  thf('60', plain,
% 0.66/0.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.66/0.87          | (r1_tarski @ 
% 0.66/0.87             (k2_pre_topc @ X26 @ 
% 0.66/0.87              (k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ X27)) @ 
% 0.66/0.87             (k9_subset_1 @ (u1_struct_0 @ X26) @ (k2_pre_topc @ X26 @ X25) @ 
% 0.66/0.87              (k2_pre_topc @ X26 @ X27)))
% 0.66/0.87          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.66/0.87          | ~ (l1_pre_topc @ X26))),
% 0.66/0.87      inference('cnf', [status(esa)], [t51_pre_topc])).
% 0.66/0.87  thf('61', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (l1_pre_topc @ sk_A)
% 0.66/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.87          | (r1_tarski @ 
% 0.66/0.87             (k2_pre_topc @ sk_A @ 
% 0.66/0.87              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.66/0.87             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.87              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.66/0.87      inference('sup-', [status(thm)], ['59', '60'])).
% 0.66/0.87  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('63', plain,
% 0.66/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.87  thf('64', plain,
% 0.66/0.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.66/0.87         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.66/0.87          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.66/0.87      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.66/0.87  thf('65', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.66/0.87           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.66/0.87      inference('sup-', [status(thm)], ['63', '64'])).
% 0.66/0.87  thf('66', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.66/0.87           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.87  thf('67', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k3_xboole_0 @ X0 @ sk_B)
% 0.66/0.87           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.66/0.87      inference('demod', [status(thm)], ['65', '66'])).
% 0.66/0.87  thf('68', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.66/0.87  thf('69', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         ((k3_xboole_0 @ X0 @ sk_B)
% 0.66/0.87           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.66/0.87      inference('demod', [status(thm)], ['65', '66'])).
% 0.66/0.87  thf('70', plain,
% 0.66/0.87      (![X0 : $i]:
% 0.66/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.87          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 0.66/0.87             (k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_B)))),
% 0.66/0.87      inference('demod', [status(thm)], ['61', '62', '67', '68', '69'])).
% 0.66/0.87  thf('71', plain,
% 0.66/0.87      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 0.66/0.87        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ sk_B))),
% 0.66/0.87      inference('sup-', [status(thm)], ['58', '70'])).
% 0.66/0.87  thf('72', plain,
% 0.66/0.87      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['18', '21'])).
% 0.66/0.87  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.66/0.87  thf('74', plain,
% 0.66/0.87      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.66/0.87      inference('demod', [status(thm)], ['18', '21'])).
% 0.66/0.87  thf('75', plain,
% 0.66/0.87      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.66/0.87        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.87      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.66/0.87  thf('76', plain, ($false), inference('demod', [status(thm)], ['57', '75'])).
% 0.66/0.87  
% 0.66/0.87  % SZS output end Refutation
% 0.66/0.87  
% 0.66/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
