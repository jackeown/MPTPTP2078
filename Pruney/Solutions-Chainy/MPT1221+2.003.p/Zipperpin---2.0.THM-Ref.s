%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KqWaz6JBtL

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:42 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  173 (1396 expanded)
%              Number of leaves         :   39 ( 438 expanded)
%              Depth                    :   23
%              Number of atoms          : 1370 (12361 expanded)
%              Number of equality atoms :   79 ( 628 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X26 @ X24 )
        = ( k9_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('14',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['40','43'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['28','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('54',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','26'])).

thf('56',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('59',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('63',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('66',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('67',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('69',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','72'])).

thf('74',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('81',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('82',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('84',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('86',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('88',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('89',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['74','89'])).

thf('91',plain,
    ( ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('93',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('97',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['93','101'])).

thf('103',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('105',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('106',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,
    ( ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('111',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('114',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('116',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('117',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('118',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('122',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('124',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('125',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','112','113','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KqWaz6JBtL
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 516 iterations in 0.183s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.44/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.63  thf(t29_tops_1, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.63             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( l1_pre_topc @ A ) =>
% 0.44/0.63          ( ![B:$i]:
% 0.44/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63              ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.63                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.44/0.63        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.44/0.63       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf(d3_struct_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X29 : $i]:
% 0.44/0.63         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.63  thf(dt_k2_subset_1, axiom,
% 0.44/0.63    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.44/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.44/0.63  thf('4', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.44/0.64      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.44/0.64  thf('5', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.44/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.44/0.64  thf('6', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t32_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ![C:$i]:
% 0.44/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.44/0.64             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.44/0.64  thf('7', plain,
% 0.44/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.44/0.64          | ((k7_subset_1 @ X25 @ X26 @ X24)
% 0.44/0.64              = (k9_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X24)))
% 0.44/0.64          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.44/0.64  thf('8', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.64          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.64              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.44/0.64                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(d5_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      (![X13 : $i, X14 : $i]:
% 0.44/0.64         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.44/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.64  thf('12', plain,
% 0.44/0.64      (![X29 : $i]:
% 0.44/0.64         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.64  thf('14', plain,
% 0.44/0.64      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.44/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.44/0.64  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(dt_l1_pre_topc, axiom,
% 0.44/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.64  thf('16', plain,
% 0.44/0.64      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.64  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['14', '17'])).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      (![X29 : $i]:
% 0.44/0.64         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.64  thf('20', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('21', plain,
% 0.44/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.44/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.64      inference('sup+', [status(thm)], ['19', '20'])).
% 0.44/0.64  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('23', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.64  thf('24', plain,
% 0.44/0.64      (![X13 : $i, X14 : $i]:
% 0.44/0.64         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.44/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.64  thf('25', plain,
% 0.44/0.64      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.64  thf('26', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['18', '25'])).
% 0.44/0.64  thf('27', plain,
% 0.44/0.64      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['11', '26'])).
% 0.44/0.64  thf('28', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.64          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.64              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.44/0.64                 (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('demod', [status(thm)], ['8', '27'])).
% 0.44/0.64  thf('29', plain,
% 0.44/0.64      (![X29 : $i]:
% 0.44/0.64         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.64  thf(d3_tarski, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.64  thf('30', plain,
% 0.44/0.64      (![X1 : $i, X3 : $i]:
% 0.44/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.64  thf('31', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(l3_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.64  thf('32', plain,
% 0.44/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X18 @ X19)
% 0.44/0.64          | (r2_hidden @ X18 @ X20)
% 0.44/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.44/0.64      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r1_tarski @ sk_B @ X0)
% 0.44/0.64          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['30', '33'])).
% 0.44/0.64  thf('35', plain,
% 0.44/0.64      (![X1 : $i, X3 : $i]:
% 0.44/0.64         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.64  thf('36', plain,
% 0.44/0.64      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.44/0.64        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.64  thf('37', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.64      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.64  thf('38', plain,
% 0.44/0.64      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.64      inference('sup+', [status(thm)], ['29', '37'])).
% 0.44/0.64  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('40', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.64  thf(t28_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.64  thf('41', plain,
% 0.44/0.64      (![X6 : $i, X7 : $i]:
% 0.44/0.64         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.44/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.64  thf(t12_setfam_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.64  thf('42', plain,
% 0.44/0.64      (![X27 : $i, X28 : $i]:
% 0.44/0.64         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.44/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.64  thf('43', plain,
% 0.44/0.64      (![X6 : $i, X7 : $i]:
% 0.44/0.64         (((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (X6))
% 0.44/0.64          | ~ (r1_tarski @ X6 @ X7))),
% 0.44/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.64  thf('44', plain,
% 0.44/0.64      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))) = (sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['40', '43'])).
% 0.44/0.64  thf(commutativity_k2_tarski, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.44/0.64  thf('45', plain,
% 0.44/0.64      (![X10 : $i, X11 : $i]:
% 0.44/0.64         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.44/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.64  thf(t100_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.64  thf('46', plain,
% 0.44/0.64      (![X4 : $i, X5 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X4 @ X5)
% 0.44/0.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.64  thf('47', plain,
% 0.44/0.64      (![X27 : $i, X28 : $i]:
% 0.44/0.64         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.44/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.64  thf('48', plain,
% 0.44/0.64      (![X4 : $i, X5 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X4 @ X5)
% 0.44/0.64           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.44/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.64  thf('49', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.64           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.44/0.64      inference('sup+', [status(thm)], ['45', '48'])).
% 0.44/0.64  thf('50', plain,
% 0.44/0.64      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['44', '49'])).
% 0.44/0.64  thf('51', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.64          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.64              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.44/0.64                 (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('demod', [status(thm)], ['28', '50'])).
% 0.44/0.64  thf('52', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(dt_k3_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.44/0.64  thf('53', plain,
% 0.44/0.64      (![X16 : $i, X17 : $i]:
% 0.44/0.64         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.44/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.44/0.64  thf('54', plain,
% 0.44/0.64      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.44/0.64  thf('55', plain,
% 0.44/0.64      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['11', '26'])).
% 0.44/0.64  thf('56', plain,
% 0.44/0.64      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['54', '55'])).
% 0.44/0.64  thf('57', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.64      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.64  thf('58', plain,
% 0.44/0.64      (![X6 : $i, X7 : $i]:
% 0.44/0.64         (((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (X6))
% 0.44/0.64          | ~ (r1_tarski @ X6 @ X7))),
% 0.44/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.64  thf('59', plain,
% 0.44/0.64      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.64  thf('60', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.64           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.44/0.64      inference('sup+', [status(thm)], ['45', '48'])).
% 0.44/0.64  thf('61', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.44/0.64  thf('62', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['18', '25'])).
% 0.44/0.64  thf('63', plain,
% 0.44/0.64      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['61', '62'])).
% 0.44/0.64  thf('64', plain,
% 0.44/0.64      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['56', '63'])).
% 0.44/0.64  thf('65', plain,
% 0.44/0.64      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['44', '49'])).
% 0.44/0.64  thf('66', plain,
% 0.44/0.64      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['61', '62'])).
% 0.44/0.64  thf('67', plain,
% 0.44/0.64      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.44/0.64  thf('68', plain,
% 0.44/0.64      ((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['64', '67'])).
% 0.44/0.64  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.64  thf('69', plain,
% 0.44/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.64         (((k9_subset_1 @ X23 @ X21 @ X22) = (k3_xboole_0 @ X21 @ X22))
% 0.44/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.64  thf('70', plain,
% 0.44/0.64      (![X27 : $i, X28 : $i]:
% 0.44/0.64         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.44/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.64  thf('71', plain,
% 0.44/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.64         (((k9_subset_1 @ X23 @ X21 @ X22)
% 0.44/0.64            = (k1_setfam_1 @ (k2_tarski @ X21 @ X22)))
% 0.44/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.44/0.64      inference('demod', [status(thm)], ['69', '70'])).
% 0.44/0.64  thf('72', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.44/0.64           (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.44/0.64           = (k1_setfam_1 @ 
% 0.44/0.64              (k2_tarski @ X0 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['68', '71'])).
% 0.44/0.64  thf('73', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.64          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.64              = (k1_setfam_1 @ 
% 0.44/0.64                 (k2_tarski @ X0 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.44/0.64      inference('demod', [status(thm)], ['51', '72'])).
% 0.44/0.64  thf('74', plain,
% 0.44/0.64      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k1_setfam_1 @ 
% 0.44/0.64            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.64             (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['5', '73'])).
% 0.44/0.64  thf('75', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.44/0.64  thf(t48_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.64  thf('76', plain,
% 0.44/0.64      (![X8 : $i, X9 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.44/0.64           = (k3_xboole_0 @ X8 @ X9))),
% 0.44/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.64  thf('77', plain,
% 0.44/0.64      (![X27 : $i, X28 : $i]:
% 0.44/0.64         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.44/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.64  thf('78', plain,
% 0.44/0.64      (![X8 : $i, X9 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.44/0.64           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 0.44/0.64      inference('demod', [status(thm)], ['76', '77'])).
% 0.44/0.64  thf('79', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.64         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.44/0.64         = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['75', '78'])).
% 0.44/0.64  thf('80', plain,
% 0.44/0.64      (![X10 : $i, X11 : $i]:
% 0.44/0.64         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.44/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.64  thf('81', plain,
% 0.44/0.64      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.64  thf('82', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.64         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.44/0.64  thf('83', plain,
% 0.44/0.64      (![X8 : $i, X9 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.44/0.64           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 0.44/0.64      inference('demod', [status(thm)], ['76', '77'])).
% 0.44/0.64  thf('84', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k1_setfam_1 @ 
% 0.44/0.64            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.64             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('sup+', [status(thm)], ['82', '83'])).
% 0.44/0.64  thf('85', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.44/0.64  thf('86', plain,
% 0.44/0.64      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k1_setfam_1 @ 
% 0.44/0.64            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.64             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('demod', [status(thm)], ['84', '85'])).
% 0.44/0.64  thf('87', plain,
% 0.44/0.64      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.44/0.64  thf('88', plain,
% 0.44/0.64      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.44/0.64  thf('89', plain,
% 0.44/0.64      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k1_setfam_1 @ 
% 0.44/0.64            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.64             (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.64      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.44/0.64  thf('90', plain,
% 0.44/0.64      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['74', '89'])).
% 0.44/0.64  thf('91', plain,
% 0.44/0.64      ((((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.44/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.64      inference('sup+', [status(thm)], ['2', '90'])).
% 0.44/0.64  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('93', plain,
% 0.44/0.64      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['91', '92'])).
% 0.44/0.64  thf('94', plain,
% 0.44/0.64      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.44/0.64        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('95', plain,
% 0.44/0.64      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.64      inference('split', [status(esa)], ['94'])).
% 0.44/0.64  thf('96', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(d6_pre_topc, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( l1_pre_topc @ A ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.64           ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.64             ( v3_pre_topc @
% 0.44/0.64               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.44/0.64               A ) ) ) ) ))).
% 0.44/0.64  thf('97', plain,
% 0.44/0.64      (![X30 : $i, X31 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.44/0.64          | ~ (v4_pre_topc @ X30 @ X31)
% 0.44/0.64          | (v3_pre_topc @ 
% 0.44/0.64             (k7_subset_1 @ (u1_struct_0 @ X31) @ (k2_struct_0 @ X31) @ X30) @ 
% 0.44/0.64             X31)
% 0.44/0.64          | ~ (l1_pre_topc @ X31))),
% 0.44/0.64      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.44/0.64  thf('98', plain,
% 0.44/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.64        | (v3_pre_topc @ 
% 0.44/0.64           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64           sk_A)
% 0.44/0.64        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['96', '97'])).
% 0.44/0.64  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('100', plain,
% 0.44/0.64      (((v3_pre_topc @ 
% 0.44/0.64         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64         sk_A)
% 0.44/0.64        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['98', '99'])).
% 0.44/0.64  thf('101', plain,
% 0.44/0.64      (((v3_pre_topc @ 
% 0.44/0.64         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.44/0.64         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['95', '100'])).
% 0.44/0.64  thf('102', plain,
% 0.44/0.64      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['93', '101'])).
% 0.44/0.64  thf('103', plain,
% 0.44/0.64      (![X29 : $i]:
% 0.44/0.64         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.64  thf('104', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.44/0.64  thf('105', plain,
% 0.44/0.64      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.64  thf('106', plain,
% 0.44/0.64      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (~
% 0.44/0.64             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('split', [status(esa)], ['0'])).
% 0.44/0.64  thf('107', plain,
% 0.44/0.64      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (~
% 0.44/0.64             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.64  thf('108', plain,
% 0.44/0.64      ((~ (v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (~
% 0.44/0.64             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['104', '107'])).
% 0.44/0.64  thf('109', plain,
% 0.44/0.64      (((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.44/0.64         | ~ (l1_struct_0 @ sk_A)))
% 0.44/0.64         <= (~
% 0.44/0.64             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['103', '108'])).
% 0.44/0.64  thf('110', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('111', plain,
% 0.44/0.64      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (~
% 0.44/0.64             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['109', '110'])).
% 0.44/0.64  thf('112', plain,
% 0.44/0.64      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.44/0.64       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['102', '111'])).
% 0.44/0.64  thf('113', plain,
% 0.44/0.64      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.44/0.64       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('split', [status(esa)], ['94'])).
% 0.44/0.64  thf('114', plain,
% 0.44/0.64      (![X29 : $i]:
% 0.44/0.64         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.64  thf('115', plain,
% 0.44/0.64      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.44/0.64  thf('116', plain,
% 0.44/0.64      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.64  thf('117', plain,
% 0.44/0.64      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('split', [status(esa)], ['94'])).
% 0.44/0.64  thf('118', plain,
% 0.44/0.64      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['116', '117'])).
% 0.44/0.64  thf('119', plain,
% 0.44/0.64      (((v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['115', '118'])).
% 0.44/0.64  thf('120', plain,
% 0.44/0.64      ((((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.44/0.64         | ~ (l1_struct_0 @ sk_A)))
% 0.44/0.64         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['114', '119'])).
% 0.44/0.64  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.64  thf('122', plain,
% 0.44/0.64      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.44/0.64         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['120', '121'])).
% 0.44/0.64  thf('123', plain,
% 0.44/0.64      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.44/0.64         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['91', '92'])).
% 0.44/0.64  thf('124', plain,
% 0.44/0.64      (![X30 : $i, X31 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.44/0.64          | ~ (v3_pre_topc @ 
% 0.44/0.64               (k7_subset_1 @ (u1_struct_0 @ X31) @ (k2_struct_0 @ X31) @ X30) @ 
% 0.44/0.64               X31)
% 0.44/0.64          | (v4_pre_topc @ X30 @ X31)
% 0.44/0.64          | ~ (l1_pre_topc @ X31))),
% 0.44/0.64      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.44/0.64  thf('125', plain,
% 0.44/0.64      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.44/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.64        | (v4_pre_topc @ sk_B @ sk_A)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['123', '124'])).
% 0.44/0.64  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('127', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('128', plain,
% 0.44/0.64      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.44/0.64        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.44/0.64  thf('129', plain,
% 0.44/0.64      (((v4_pre_topc @ sk_B @ sk_A))
% 0.44/0.64         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['122', '128'])).
% 0.44/0.64  thf('130', plain,
% 0.44/0.64      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.64      inference('split', [status(esa)], ['0'])).
% 0.44/0.64  thf('131', plain,
% 0.44/0.64      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.44/0.64       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['129', '130'])).
% 0.44/0.64  thf('132', plain, ($false),
% 0.44/0.64      inference('sat_resolution*', [status(thm)], ['1', '112', '113', '131'])).
% 0.44/0.64  
% 0.44/0.64  % SZS output end Refutation
% 0.44/0.64  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
