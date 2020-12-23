%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWlqCPa2e0

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:43 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 341 expanded)
%              Number of leaves         :   34 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  735 (3243 expanded)
%              Number of equality atoms :   51 ( 209 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','26'])).

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

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( v3_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('43',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['47','48','53','54'])).

thf('56',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','44','55'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('57',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('58',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('59',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['12','56','67'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWlqCPa2e0
% 0.15/0.36  % Computer   : n016.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:14:49 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 117 iterations in 0.055s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.35/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.35/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(d3_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X12 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf(t97_tops_1, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.35/0.53             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.35/0.53                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.35/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_l1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('4', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.53  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '5'])).
% 0.35/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]:
% 0.35/0.53         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.35/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.53         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '5'])).
% 0.35/0.53  thf(d5_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.35/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.53         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_k3_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i]:
% 0.35/0.53         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.35/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.35/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X12 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '23'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '26'])).
% 0.35/0.53  thf(t52_pre_topc, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.35/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.35/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.53          | ~ (v4_pre_topc @ X14 @ X15)
% 0.35/0.53          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.35/0.53          | ~ (l1_pre_topc @ X15))),
% 0.35/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53            = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53        | ~ (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53        | ~ (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '26'])).
% 0.35/0.53  thf(d3_tops_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.35/0.53             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.53          | ~ (v1_tops_1 @ X16 @ X17)
% 0.35/0.53          | ((k2_pre_topc @ X17 @ X16) = (k2_struct_0 @ X17))
% 0.35/0.53          | ~ (l1_pre_topc @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53            = (k2_struct_0 @ sk_A))
% 0.35/0.53        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.53  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53          = (k2_struct_0 @ sk_A))
% 0.35/0.53        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t91_tops_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( v3_tops_1 @ B @ A ) =>
% 0.35/0.53             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.35/0.53          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.35/0.53          | ~ (v3_tops_1 @ X20 @ X21)
% 0.35/0.53          | ~ (l1_pre_topc @ X21))),
% 0.35/0.53      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.35/0.53        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('41', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      ((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.35/0.53         = (k2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['36', '43'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '26'])).
% 0.35/0.53  thf(t29_tops_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.35/0.53             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.35/0.53          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.35/0.53          | (v4_pre_topc @ X18 @ X19)
% 0.35/0.53          | ~ (l1_pre_topc @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.35/0.53        | ~ (v3_pre_topc @ 
% 0.35/0.53             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.53              (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.35/0.53             sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.53  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]:
% 0.35/0.53         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.35/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.35/0.53         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('53', plain,
% 0.35/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.53         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.35/0.53  thf('54', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      ((v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.35/0.53      inference('demod', [status(thm)], ['47', '48', '53', '54'])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      (((k2_struct_0 @ sk_A) = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['31', '44', '55'])).
% 0.35/0.53  thf(dt_k2_subset_1, axiom,
% 0.35/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.53  thf('57', plain,
% 0.35/0.53      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.35/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.53  thf('58', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.53  thf('59', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.35/0.53      inference('demod', [status(thm)], ['57', '58'])).
% 0.35/0.53  thf('60', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.35/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.53  thf('61', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.53  thf(t3_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.53  thf('62', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.35/0.53  thf(t48_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('63', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.35/0.53           = (k3_xboole_0 @ X2 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.53  thf('64', plain,
% 0.35/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.35/0.53  thf(t2_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('65', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.35/0.53  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.35/0.53  thf('67', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['61', '66'])).
% 0.35/0.53  thf('68', plain, (((k1_xboole_0) = (sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['12', '56', '67'])).
% 0.35/0.53  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('70', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
