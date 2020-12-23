%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RKpvcBfETe

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 288 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  657 (3023 expanded)
%              Number of equality atoms :   39 ( 155 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t59_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
              = ( k2_pre_topc @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
                = ( k2_pre_topc @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
            = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k1_tops_1 @ X16 @ X15 ) )
        = ( k2_pre_topc @ X16 @ ( k1_tops_1 @ X16 @ ( k2_pre_topc @ X16 @ ( k1_tops_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t58_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','7','10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_pre_topc @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['20','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['35','41','42','43','44'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['35','41','42','43','44'])).

thf('47',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','45','46'])).

thf('48',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
 != ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RKpvcBfETe
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 45 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(t59_tops_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.47             ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.20/0.47               ( k2_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( l1_pre_topc @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.47                ( ( k2_pre_topc @
% 0.20/0.47                    A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.20/0.47                  ( k2_pre_topc @ A @ B ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t59_tops_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t58_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.20/0.47             ( k2_pre_topc @
% 0.20/0.47               A @ 
% 0.20/0.47               ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.47          | ((k2_pre_topc @ X16 @ (k1_tops_1 @ X16 @ X15))
% 0.20/0.47              = (k2_pre_topc @ X16 @ 
% 0.20/0.47                 (k1_tops_1 @ X16 @ 
% 0.20/0.47                  (k2_pre_topc @ X16 @ (k1_tops_1 @ X16 @ X15)))))
% 0.20/0.47          | ~ (l1_pre_topc @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t58_tops_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.47            = (k2_pre_topc @ sk_A @ 
% 0.20/0.47               (k1_tops_1 @ sk_A @ 
% 0.20/0.47                (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t30_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.47             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.47          | ~ (v3_pre_topc @ X13 @ X14)
% 0.20/0.47          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 0.20/0.47          | ~ (l1_pre_topc @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.47        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d5_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '10', '11'])).
% 0.20/0.47  thf(t36_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.47  thf(t3_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X6 : $i, X8 : $i]:
% 0.20/0.47         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(t52_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.47             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.47               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.47          | ~ (v4_pre_topc @ X9 @ X10)
% 0.20/0.47          | ((k2_pre_topc @ X10 @ X9) = (X9))
% 0.20/0.47          | ~ (l1_pre_topc @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.20/0.47              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.20/0.47          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.47  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(d1_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( k1_tops_1 @ A @ B ) =
% 0.20/0.47             ( k3_subset_1 @
% 0.20/0.47               ( u1_struct_0 @ A ) @ 
% 0.20/0.47               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.47          | ((k1_tops_1 @ X12 @ X11)
% 0.20/0.47              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.47                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 0.20/0.47          | ~ (l1_pre_topc @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.20/0.47              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.47                 (k2_pre_topc @ X0 @ 
% 0.20/0.47                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.47                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.20/0.47              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.47                 (k2_pre_topc @ X0 @ 
% 0.20/0.47                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.20/0.47                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k1_tops_1 @ X1 @ 
% 0.20/0.47            (k4_xboole_0 @ (u1_struct_0 @ X1) @ 
% 0.20/0.47             (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0)))
% 0.20/0.47            = (k3_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.20/0.47               (k2_pre_topc @ X1 @ (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0))))
% 0.20/0.47          | ~ (l1_pre_topc @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['28', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((k1_tops_1 @ sk_A @ 
% 0.20/0.47          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.47          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['20', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.47           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.47  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('45', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '41', '42', '43', '44'])).
% 0.20/0.47  thf('46', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '41', '42', '43', '44'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.47         = (k2_pre_topc @ sk_A @ 
% 0.20/0.47            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3', '45', '46'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.47         != (k2_pre_topc @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('49', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
