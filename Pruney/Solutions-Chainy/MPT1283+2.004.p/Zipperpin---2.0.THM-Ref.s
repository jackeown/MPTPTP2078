%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7shZXFEHe

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:52 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 323 expanded)
%              Number of leaves         :   29 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  895 (3104 expanded)
%              Number of equality atoms :   54 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t105_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( ( v5_tops_1 @ B @ A )
            <=> ( v6_tops_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v4_pre_topc @ B @ A ) )
             => ( ( v5_tops_1 @ B @ A )
              <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t105_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('9',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X15 @ X14 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','18'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ( v4_pre_topc @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ( ( k2_pre_topc @ X13 @ X12 )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','43','44'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['19','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18
       != ( k1_tops_1 @ X19 @ ( k2_pre_topc @ X19 @ X18 ) ) )
      | ( v6_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ( ( k2_pre_topc @ X13 @ X12 )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','56'])).

thf('58',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
   <= ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v6_tops_1 @ X18 @ X19 )
      | ( X18
        = ( k1_tops_1 @ X19 @ ( k2_pre_topc @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('68',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X16
       != ( k2_pre_topc @ X17 @ ( k1_tops_1 @ X17 @ X16 ) ) )
      | ( v5_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( sk_B
       != ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v5_tops_1 @ sk_B @ sk_A ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('77',plain,
    ( ( ( sk_B != sk_B )
      | ( v5_tops_1 @ sk_B @ sk_A ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v5_tops_1 @ sk_B @ sk_A )
   <= ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('80',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['60','80'])).

thf('82',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','81'])).

thf('83',plain,(
    sk_B
 != ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['57','82'])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7shZXFEHe
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 230 iterations in 0.137s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.59  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.38/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.59  thf(t105_tops_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.38/0.59             ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( l1_pre_topc @ A ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59              ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.38/0.59                ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t105_tops_1])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(involutiveness_k3_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i]:
% 0.38/0.59         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.38/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.38/0.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d5_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i]:
% 0.38/0.59         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.38/0.59         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['2', '5'])).
% 0.38/0.59  thf(dt_k2_subset_1, axiom,
% 0.38/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.59  thf('8', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.59  thf('9', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf(dt_k7_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.38/0.59          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i]:
% 0.38/0.59         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k3_subset_1 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1))
% 0.38/0.59           = (k4_xboole_0 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.59  thf('14', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf(redefinition_k7_subset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.38/0.59          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.38/0.59           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['6', '18'])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d1_tops_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( k1_tops_1 @ A @ B ) =
% 0.38/0.59             ( k3_subset_1 @
% 0.38/0.59               ( u1_struct_0 @ A ) @ 
% 0.38/0.59               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X14 : $i, X15 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.59          | ((k1_tops_1 @ X15 @ X14)
% 0.38/0.59              = (k3_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.38/0.59                 (k2_pre_topc @ X15 @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14))))
% 0.38/0.59          | ~ (l1_pre_topc @ X15))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.38/0.59            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59               (k2_pre_topc @ sk_A @ 
% 0.38/0.59                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.59  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.38/0.59         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (((k1_tops_1 @ sk_A @ sk_B)
% 0.38/0.59         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.59      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['6', '18'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf(t29_tops_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.59             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (![X22 : $i, X23 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.59          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.38/0.59          | (v4_pre_topc @ X22 @ X23)
% 0.38/0.59          | ~ (l1_pre_topc @ X23))),
% 0.38/0.59      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X0)
% 0.38/0.59          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.38/0.59          | ~ (v3_pre_topc @ 
% 0.38/0.59               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.59                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.38/0.59               X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.38/0.59           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X0)
% 0.38/0.59          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.38/0.59          | ~ (v3_pre_topc @ 
% 0.38/0.59               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.38/0.59                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.38/0.59               X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['26', '33'])).
% 0.38/0.59  thf('35', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf(t52_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.59          | ~ (v4_pre_topc @ X12 @ X13)
% 0.38/0.59          | ((k2_pre_topc @ X13 @ X12) = (X12))
% 0.38/0.59          | ~ (l1_pre_topc @ X13))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X0)
% 0.38/0.59          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.38/0.59              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.38/0.59          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['37', '40'])).
% 0.38/0.59  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.59         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.38/0.59           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['13', '16', '17'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (((k1_tops_1 @ sk_A @ sk_B)
% 0.38/0.59         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.59            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['25', '43', '44'])).
% 0.38/0.59  thf('46', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.59      inference('sup+', [status(thm)], ['19', '45'])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d8_tops_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( v6_tops_1 @ B @ A ) <=>
% 0.38/0.59             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.59          | ((X18) != (k1_tops_1 @ X19 @ (k2_pre_topc @ X19 @ X18)))
% 0.38/0.59          | (v6_tops_1 @ X18 @ X19)
% 0.38/0.59          | ~ (l1_pre_topc @ X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v6_tops_1 @ sk_B @ sk_A)
% 0.38/0.59        | ((sk_B) != (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.59          | ~ (v4_pre_topc @ X12 @ X13)
% 0.38/0.59          | ((k2_pre_topc @ X13 @ X12) = (X12))
% 0.38/0.59          | ~ (l1_pre_topc @ X13))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.38/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.59  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('55', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('56', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '50', '56'])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      ((~ (v6_tops_1 @ sk_B @ sk_A) | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('59', plain,
% 0.38/0.59      ((~ (v6_tops_1 @ sk_B @ sk_A)) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['58'])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (~ ((v6_tops_1 @ sk_B @ sk_A)) | ~ ((v5_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('split', [status(esa)], ['58'])).
% 0.38/0.59  thf('61', plain, (((v6_tops_1 @ sk_B @ sk_A) | (v5_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (((v6_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['61'])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.59          | ~ (v6_tops_1 @ X18 @ X19)
% 0.38/0.59          | ((X18) = (k1_tops_1 @ X19 @ (k2_pre_topc @ X19 @ X18)))
% 0.38/0.59          | ~ (l1_pre_topc @ X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.38/0.59        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.59  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('67', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)) | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B))) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['62', '68'])).
% 0.38/0.59  thf('70', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d7_tops_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( v5_tops_1 @ B @ A ) <=>
% 0.38/0.59             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('71', plain,
% 0.38/0.59      (![X16 : $i, X17 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.59          | ((X16) != (k2_pre_topc @ X17 @ (k1_tops_1 @ X17 @ X16)))
% 0.38/0.59          | (v5_tops_1 @ X16 @ X17)
% 0.38/0.59          | ~ (l1_pre_topc @ X17))),
% 0.38/0.59      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.38/0.59  thf('72', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v5_tops_1 @ sk_B @ sk_A)
% 0.38/0.59        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.59  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      (((v5_tops_1 @ sk_B @ sk_A)
% 0.38/0.59        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.59      inference('demod', [status(thm)], ['72', '73'])).
% 0.38/0.59  thf('75', plain,
% 0.38/0.59      (((((sk_B) != (k2_pre_topc @ sk_A @ sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.38/0.59         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['69', '74'])).
% 0.38/0.59  thf('76', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.38/0.59  thf('77', plain,
% 0.38/0.59      (((((sk_B) != (sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.38/0.59         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['75', '76'])).
% 0.38/0.59  thf('78', plain,
% 0.38/0.59      (((v5_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['77'])).
% 0.38/0.59  thf('79', plain,
% 0.38/0.59      ((~ (v5_tops_1 @ sk_B @ sk_A)) <= (~ ((v5_tops_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('split', [status(esa)], ['58'])).
% 0.38/0.59  thf('80', plain,
% 0.38/0.59      (((v5_tops_1 @ sk_B @ sk_A)) | ~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.59  thf('81', plain, (~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['60', '80'])).
% 0.38/0.59  thf('82', plain, (~ (v6_tops_1 @ sk_B @ sk_A)),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['59', '81'])).
% 0.38/0.59  thf('83', plain, (((sk_B) != (k1_tops_1 @ sk_A @ sk_B))),
% 0.38/0.59      inference('clc', [status(thm)], ['57', '82'])).
% 0.38/0.59  thf('84', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['46', '83'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
