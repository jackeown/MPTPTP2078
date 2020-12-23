%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4VIQ7s04QQ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 167 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  673 (1781 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t56_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( r1_tarski @ B @ C ) )
                 => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['8','9','12','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_pre_topc @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['22','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4VIQ7s04QQ
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:48:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 94 iterations in 0.043s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(t56_tops_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.48                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( l1_pre_topc @ A ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48                  ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.48                    ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t56_tops_1])).
% 0.19/0.48  thf('0', plain, (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t48_tops_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48               ( ( r1_tarski @ B @ C ) =>
% 0.19/0.48                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.48          | ~ (r1_tarski @ X15 @ X17)
% 0.19/0.48          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 0.19/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.48          | ~ (l1_pre_topc @ X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.19/0.48          | ~ (r1_tarski @ sk_B @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t30_tops_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ( v3_pre_topc @ B @ A ) <=>
% 0.19/0.48             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.48          | ~ (v3_pre_topc @ X13 @ X14)
% 0.19/0.48          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.19/0.48          | ~ (l1_pre_topc @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.48        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d5_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.19/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.19/0.48         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '9', '12', '13'])).
% 0.19/0.48  thf(t36_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.48  thf(t3_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X6 : $i, X8 : $i]:
% 0.19/0.48         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf(t52_pre_topc, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.19/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.19/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.19/0.48          | ~ (v4_pre_topc @ X9 @ X10)
% 0.19/0.48          | ((k2_pre_topc @ X10 @ X9) = (X9))
% 0.19/0.48          | ~ (l1_pre_topc @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.19/0.48              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.19/0.48          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '19'])).
% 0.19/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.48       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.19/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.19/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '28', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf(d1_tops_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.48           ( ( k1_tops_1 @ A @ B ) =
% 0.19/0.48             ( k3_subset_1 @
% 0.19/0.48               ( u1_struct_0 @ A ) @ 
% 0.19/0.48               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.48          | ((k1_tops_1 @ X12 @ X11)
% 0.19/0.48              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.19/0.48                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 0.19/0.48          | ~ (l1_pre_topc @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.19/0.48              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.19/0.48                 (k2_pre_topc @ X0 @ 
% 0.19/0.48                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.19/0.48                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (l1_pre_topc @ X0)
% 0.19/0.48          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.19/0.48              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.19/0.48                 (k2_pre_topc @ X0 @ 
% 0.19/0.48                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.19/0.48                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_tops_1 @ X1 @ 
% 0.19/0.48            (k4_xboole_0 @ (u1_struct_0 @ X1) @ 
% 0.19/0.48             (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0)))
% 0.19/0.48            = (k3_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.19/0.48               (k2_pre_topc @ X1 @ (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0))))
% 0.19/0.48          | ~ (l1_pre_topc @ X1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['30', '35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      ((((k1_tops_1 @ sk_A @ 
% 0.19/0.48          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['22', '36'])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.19/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.19/0.48         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.48           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.48         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.19/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('47', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['37', '43', '44', '45', '46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.48          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.19/0.48          | ~ (r1_tarski @ sk_B @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.19/0.48        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '48'])).
% 0.19/0.48  thf('50', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('51', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.48  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
