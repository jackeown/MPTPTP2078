%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bro48gTBSd

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 365 expanded)
%              Number of leaves         :   26 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  979 (3791 expanded)
%              Number of equality atoms :   51 ( 125 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('0',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
   <= ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13
       != ( k2_pre_topc @ X14 @ ( k1_tops_1 @ X14 @ X13 ) ) )
      | ( v5_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_pre_topc @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['32','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','11','16'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','11','16'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['4','5','50','56'])).

thf('58',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( v5_tops_1 @ sk_B @ sk_A )
   <= ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v6_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('69',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','11','16'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('72',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13
       != ( k2_pre_topc @ X14 @ ( k1_tops_1 @ X14 @ X13 ) ) )
      | ( v5_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_pre_topc @ X0 @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
     != ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
     != ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['69','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['63','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bro48gTBSd
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:36:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 77 iterations in 0.028s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.46  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.46  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.22/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.46  thf(t105_tops_1, conjecture,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.22/0.46             ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i]:
% 0.22/0.46        ( ( l1_pre_topc @ A ) =>
% 0.22/0.46          ( ![B:$i]:
% 0.22/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46              ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.22/0.46                ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t105_tops_1])).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      ((~ (v6_tops_1 @ sk_B @ sk_A) | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      ((~ (v6_tops_1 @ sk_B @ sk_A)) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.46      inference('split', [status(esa)], ['0'])).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(d7_tops_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( v5_tops_1 @ B @ A ) <=>
% 0.22/0.46             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.46          | ((X13) != (k2_pre_topc @ X14 @ (k1_tops_1 @ X14 @ X13)))
% 0.22/0.46          | (v5_tops_1 @ X13 @ X14)
% 0.22/0.46          | ~ (l1_pre_topc @ X14))),
% 0.22/0.46      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.46        | (v5_tops_1 @ sk_B @ sk_A)
% 0.22/0.46        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.22/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.46      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(d5_subset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i]:
% 0.22/0.46         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.22/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.46         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf(t36_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.46  thf(t3_subset, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (![X6 : $i, X8 : $i]:
% 0.22/0.46         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i]:
% 0.22/0.46         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.22/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['8', '11', '16'])).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf(t29_tops_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( v4_pre_topc @ B @ A ) <=>
% 0.22/0.46             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (![X17 : $i, X18 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.46          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.22/0.46          | (v4_pre_topc @ X17 @ X18)
% 0.22/0.46          | ~ (l1_pre_topc @ X18))),
% 0.22/0.46      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.22/0.46  thf('20', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.22/0.46          | ~ (v3_pre_topc @ 
% 0.22/0.46               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.22/0.46               X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.46  thf('21', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('22', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.22/0.46          | ~ (v3_pre_topc @ 
% 0.22/0.46               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.22/0.46               X0))),
% 0.22/0.46      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.46  thf('23', plain,
% 0.22/0.46      ((~ (v3_pre_topc @ sk_B @ sk_A)
% 0.22/0.46        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['17', '22'])).
% 0.22/0.46  thf('24', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('26', plain,
% 0.22/0.46      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.22/0.46      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.22/0.46  thf('27', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf(t52_pre_topc, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.46             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.46               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.46  thf('28', plain,
% 0.22/0.46      (![X9 : $i, X10 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.46          | ~ (v4_pre_topc @ X9 @ X10)
% 0.22/0.46          | ((k2_pre_topc @ X10 @ X9) = (X9))
% 0.22/0.46          | ~ (l1_pre_topc @ X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.46  thf('29', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.46              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.46          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.46  thf('30', plain,
% 0.22/0.46      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.46  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('32', plain,
% 0.22/0.46      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.46  thf('33', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf('34', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.22/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.46      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.46  thf('35', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.46  thf('36', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('37', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('38', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.46  thf('39', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf(d1_tops_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( k1_tops_1 @ A @ B ) =
% 0.22/0.46             ( k3_subset_1 @
% 0.22/0.46               ( u1_struct_0 @ A ) @ 
% 0.22/0.46               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.22/0.46  thf('40', plain,
% 0.22/0.46      (![X11 : $i, X12 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.46          | ((k1_tops_1 @ X12 @ X11)
% 0.22/0.46              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.22/0.46                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 0.22/0.46          | ~ (l1_pre_topc @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.22/0.46  thf('41', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.46              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                 (k2_pre_topc @ X0 @ 
% 0.22/0.46                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.22/0.46      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.46  thf('42', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('43', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.46              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                 (k2_pre_topc @ X0 @ 
% 0.22/0.46                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.22/0.46      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.46  thf('44', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (((k1_tops_1 @ X1 @ 
% 0.22/0.46            (k4_xboole_0 @ (u1_struct_0 @ X1) @ 
% 0.22/0.46             (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0)))
% 0.22/0.46            = (k3_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.22/0.46               (k2_pre_topc @ X1 @ (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0))))
% 0.22/0.46          | ~ (l1_pre_topc @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['38', '43'])).
% 0.22/0.46  thf('45', plain,
% 0.22/0.46      ((((k1_tops_1 @ sk_A @ 
% 0.22/0.46          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.46          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.46      inference('sup+', [status(thm)], ['32', '44'])).
% 0.22/0.46  thf('46', plain,
% 0.22/0.46      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['8', '11', '16'])).
% 0.22/0.46  thf('47', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.46           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('48', plain,
% 0.22/0.46      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['8', '11', '16'])).
% 0.22/0.46  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('50', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.22/0.46  thf('51', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('52', plain,
% 0.22/0.46      (![X9 : $i, X10 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.46          | ~ (v4_pre_topc @ X9 @ X10)
% 0.22/0.46          | ((k2_pre_topc @ X10 @ X9) = (X9))
% 0.22/0.46          | ~ (l1_pre_topc @ X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.46  thf('53', plain,
% 0.22/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.46        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.22/0.46        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.46  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('55', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('56', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.22/0.46  thf('57', plain, (((v5_tops_1 @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '5', '50', '56'])).
% 0.22/0.46  thf('58', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.22/0.46      inference('simplify', [status(thm)], ['57'])).
% 0.22/0.46  thf('59', plain,
% 0.22/0.46      ((~ (v5_tops_1 @ sk_B @ sk_A)) <= (~ ((v5_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.46      inference('split', [status(esa)], ['0'])).
% 0.22/0.46  thf('60', plain, (((v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.46  thf('61', plain,
% 0.22/0.46      (~ ((v6_tops_1 @ sk_B @ sk_A)) | ~ ((v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.46      inference('split', [status(esa)], ['0'])).
% 0.22/0.46  thf('62', plain, (~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.46      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.22/0.46  thf('63', plain, (~ (v6_tops_1 @ sk_B @ sk_A)),
% 0.22/0.46      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 0.22/0.46  thf('64', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t101_tops_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( v6_tops_1 @ B @ A ) <=>
% 0.22/0.46             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.46  thf('65', plain,
% 0.22/0.46      (![X15 : $i, X16 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.46          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15) @ X16)
% 0.22/0.46          | (v6_tops_1 @ X15 @ X16)
% 0.22/0.46          | ~ (l1_pre_topc @ X16))),
% 0.22/0.46      inference('cnf', [status(esa)], [t101_tops_1])).
% 0.22/0.46  thf('66', plain,
% 0.22/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.46        | (v6_tops_1 @ sk_B @ sk_A)
% 0.22/0.46        | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.46  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('68', plain,
% 0.22/0.46      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.46         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('69', plain,
% 0.22/0.46      (((v6_tops_1 @ sk_B @ sk_A)
% 0.22/0.46        | ~ (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.22/0.46  thf('70', plain,
% 0.22/0.46      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.46         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['8', '11', '16'])).
% 0.22/0.46  thf('71', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.46              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                 (k2_pre_topc @ X0 @ 
% 0.22/0.46                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.22/0.46                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.22/0.46      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.46  thf('72', plain,
% 0.22/0.46      ((((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.46      inference('sup+', [status(thm)], ['70', '71'])).
% 0.22/0.46  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.22/0.46  thf('74', plain,
% 0.22/0.46      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.46         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('76', plain,
% 0.22/0.46      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.22/0.46  thf('77', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf('78', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.46          | ((X13) != (k2_pre_topc @ X14 @ (k1_tops_1 @ X14 @ X13)))
% 0.22/0.46          | (v5_tops_1 @ X13 @ X14)
% 0.22/0.46          | ~ (l1_pre_topc @ X14))),
% 0.22/0.46      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.22/0.46  thf('79', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.22/0.46          | ((k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)
% 0.22/0.46              != (k2_pre_topc @ X0 @ 
% 0.22/0.46                  (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.22/0.46      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.46  thf('80', plain,
% 0.22/0.46      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.46          != (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.46        | (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.46        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['76', '79'])).
% 0.22/0.46  thf('81', plain,
% 0.22/0.46      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.46  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('83', plain,
% 0.22/0.46      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.22/0.46          != (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.46        | (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.22/0.46  thf('84', plain,
% 0.22/0.46      ((v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.22/0.46      inference('simplify', [status(thm)], ['83'])).
% 0.22/0.46  thf('85', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.22/0.46      inference('demod', [status(thm)], ['69', '84'])).
% 0.22/0.46  thf('86', plain, ($false), inference('demod', [status(thm)], ['63', '85'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
