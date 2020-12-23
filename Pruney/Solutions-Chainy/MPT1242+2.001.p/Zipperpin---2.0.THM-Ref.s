%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eGKmNJRAqA

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 176 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  678 (2006 expanded)
%              Number of equality atoms :   35 (  57 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_tops_1 @ X13 @ X12 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','31'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( ( k7_subset_1 @ X5 @ X4 @ X6 )
        = ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ ( k7_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_struct_0 @ X11 ) @ X10 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_struct_0 @ X11 ) @ X10 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t53_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','31'])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','13','32','48','53'])).

thf('55',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['9','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eGKmNJRAqA
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 96 iterations in 0.050s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(t56_tops_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_pre_topc @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                  ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                    ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t56_tops_1])).
% 0.21/0.51  thf('0', plain, (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t48_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( r1_tarski @ B @ C ) =>
% 0.21/0.51                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ~ (r1_tarski @ X14 @ X16)
% 0.21/0.51          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ (k1_tops_1 @ X15 @ X16))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.51          | ~ (l1_pre_topc @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.51          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.51          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.21/0.51        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.51  thf('8', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d1_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.51             ( k3_subset_1 @
% 0.21/0.51               ( u1_struct_0 @ A ) @ 
% 0.21/0.51               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.51          | ((k1_tops_1 @ X13 @ X12)
% 0.21/0.51              = (k3_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.51                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.51            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51               (k2_pre_topc @ sk_A @ 
% 0.21/0.51                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d5_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('21', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['25', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '31'])).
% 0.21/0.51  thf(dt_k2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X8 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.51          | ((k7_subset_1 @ X5 @ X4 @ X6) = (k4_xboole_0 @ X4 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.21/0.51              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1)
% 0.21/0.51              = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t53_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.51               ( ( k2_pre_topc @
% 0.21/0.51                   A @ 
% 0.21/0.51                   ( k7_subset_1 @
% 0.21/0.51                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.21/0.51                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 0.21/0.51             ( ( ( v2_pre_topc @ A ) & 
% 0.21/0.51                 ( ( k2_pre_topc @
% 0.21/0.51                     A @ 
% 0.21/0.51                     ( k7_subset_1 @
% 0.21/0.51                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 0.21/0.51                   ( k7_subset_1 @
% 0.21/0.51                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 0.21/0.51               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.51          | ~ (v3_pre_topc @ X10 @ X11)
% 0.21/0.51          | ((k2_pre_topc @ X11 @ 
% 0.21/0.51              (k7_subset_1 @ (u1_struct_0 @ X11) @ (k2_struct_0 @ X11) @ X10))
% 0.21/0.51              = (k7_subset_1 @ (u1_struct_0 @ X11) @ (k2_struct_0 @ X11) @ X10))
% 0.21/0.51          | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t53_pre_topc])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ 
% 0.21/0.51            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ 
% 0.21/0.51         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['36', '42'])).
% 0.21/0.51  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['35', '45'])).
% 0.21/0.51  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.51         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.51         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '31'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13', '32', '48', '53'])).
% 0.21/0.51  thf('55', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '54'])).
% 0.21/0.51  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
