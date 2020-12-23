%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZJxSc1Csps

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  625 (1731 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v5_tops_1 @ X9 @ X10 )
      | ( X9
        = ( k2_pre_topc @ X10 @ ( k1_tops_1 @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X7 @ ( k4_subset_1 @ X7 @ X8 @ X6 ) ) @ ( k3_subset_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k4_subset_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( k2_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_tops_1 @ X16 @ ( k1_tops_1 @ X16 @ X15 ) )
        = ( k2_tops_1 @ X16 @ X15 ) )
      | ~ ( v5_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30','36'])).

thf('38',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','37'])).

thf('39',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','38'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X4 @ X3 ) @ ( k3_subset_1 @ X4 @ X5 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['7','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZJxSc1Csps
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:43:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.65/1.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.82  % Solved by: fo/fo7.sh
% 1.65/1.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.82  % done 679 iterations in 1.377s
% 1.65/1.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.82  % SZS output start Refutation
% 1.65/1.82  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.82  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.65/1.82  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.65/1.82  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.65/1.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.82  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.65/1.82  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.65/1.82  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.65/1.82  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.65/1.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.82  thf(t103_tops_1, conjecture,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( l1_pre_topc @ A ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.82           ( ( v5_tops_1 @ B @ A ) =>
% 1.65/1.82             ( r1_tarski @
% 1.65/1.82               ( k2_tops_1 @ A @ B ) @ 
% 1.65/1.82               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.65/1.82  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.82    (~( ![A:$i]:
% 1.65/1.82        ( ( l1_pre_topc @ A ) =>
% 1.65/1.82          ( ![B:$i]:
% 1.65/1.82            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.82              ( ( v5_tops_1 @ B @ A ) =>
% 1.65/1.82                ( r1_tarski @
% 1.65/1.82                  ( k2_tops_1 @ A @ B ) @ 
% 1.65/1.82                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.65/1.82    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.65/1.82  thf('0', plain,
% 1.65/1.82      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('1', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(d7_tops_1, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( l1_pre_topc @ A ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.82           ( ( v5_tops_1 @ B @ A ) <=>
% 1.65/1.82             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.65/1.82  thf('2', plain,
% 1.65/1.82      (![X9 : $i, X10 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.65/1.82          | ~ (v5_tops_1 @ X9 @ X10)
% 1.65/1.82          | ((X9) = (k2_pre_topc @ X10 @ (k1_tops_1 @ X10 @ X9)))
% 1.65/1.82          | ~ (l1_pre_topc @ X10))),
% 1.65/1.82      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.65/1.82  thf('3', plain,
% 1.65/1.82      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.82        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.65/1.82        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.65/1.82      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.82  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('6', plain,
% 1.65/1.82      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.65/1.82  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.65/1.82      inference('demod', [status(thm)], ['0', '6'])).
% 1.65/1.82  thf('8', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(dt_k2_tops_1, axiom,
% 1.65/1.82    (![A:$i,B:$i]:
% 1.65/1.82     ( ( ( l1_pre_topc @ A ) & 
% 1.65/1.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.82       ( m1_subset_1 @
% 1.65/1.82         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.82  thf('9', plain,
% 1.65/1.82      (![X13 : $i, X14 : $i]:
% 1.65/1.82         (~ (l1_pre_topc @ X13)
% 1.65/1.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.65/1.82          | (m1_subset_1 @ (k2_tops_1 @ X13 @ X14) @ 
% 1.65/1.82             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 1.65/1.82      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.65/1.82  thf('10', plain,
% 1.65/1.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.82        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.82      inference('sup-', [status(thm)], ['8', '9'])).
% 1.65/1.82  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('12', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('demod', [status(thm)], ['10', '11'])).
% 1.65/1.82  thf('13', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(dt_k1_tops_1, axiom,
% 1.65/1.82    (![A:$i,B:$i]:
% 1.65/1.82     ( ( ( l1_pre_topc @ A ) & 
% 1.65/1.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.82       ( m1_subset_1 @
% 1.65/1.82         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.82  thf('14', plain,
% 1.65/1.82      (![X11 : $i, X12 : $i]:
% 1.65/1.82         (~ (l1_pre_topc @ X11)
% 1.65/1.82          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.65/1.82          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 1.65/1.82             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 1.65/1.82      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.65/1.82  thf('15', plain,
% 1.65/1.82      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.82        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.82      inference('sup-', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('17', plain,
% 1.65/1.82      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('demod', [status(thm)], ['15', '16'])).
% 1.65/1.82  thf(t41_subset_1, axiom,
% 1.65/1.82    (![A:$i,B:$i]:
% 1.65/1.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.82       ( ![C:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.82           ( r1_tarski @
% 1.65/1.82             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.65/1.82             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.65/1.82  thf('18', plain,
% 1.65/1.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.65/1.82          | (r1_tarski @ (k3_subset_1 @ X7 @ (k4_subset_1 @ X7 @ X8 @ X6)) @ 
% 1.65/1.82             (k3_subset_1 @ X7 @ X8))
% 1.65/1.82          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 1.65/1.82      inference('cnf', [status(esa)], [t41_subset_1])).
% 1.65/1.82  thf('19', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.82          | (r1_tarski @ 
% 1.65/1.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.65/1.82               (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.65/1.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['17', '18'])).
% 1.65/1.82  thf('20', plain,
% 1.65/1.82      ((r1_tarski @ 
% 1.65/1.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82          (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.65/1.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['12', '19'])).
% 1.65/1.82  thf('21', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('demod', [status(thm)], ['10', '11'])).
% 1.65/1.82  thf('22', plain,
% 1.65/1.82      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('demod', [status(thm)], ['15', '16'])).
% 1.65/1.82  thf(commutativity_k4_subset_1, axiom,
% 1.65/1.82    (![A:$i,B:$i,C:$i]:
% 1.65/1.82     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.65/1.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.65/1.82       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 1.65/1.82  thf('23', plain,
% 1.65/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.82          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 1.65/1.82          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k4_subset_1 @ X1 @ X2 @ X0)))),
% 1.65/1.82      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 1.65/1.82  thf('24', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.65/1.82            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.65/1.82               (k1_tops_1 @ sk_A @ sk_B)))
% 1.65/1.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['22', '23'])).
% 1.65/1.82  thf('25', plain,
% 1.65/1.82      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82         (k2_tops_1 @ sk_A @ sk_B))
% 1.65/1.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['21', '24'])).
% 1.65/1.82  thf('26', plain,
% 1.65/1.82      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('demod', [status(thm)], ['15', '16'])).
% 1.65/1.82  thf(t65_tops_1, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( l1_pre_topc @ A ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.82           ( ( k2_pre_topc @ A @ B ) =
% 1.65/1.82             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.82  thf('27', plain,
% 1.65/1.82      (![X17 : $i, X18 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.65/1.82          | ((k2_pre_topc @ X18 @ X17)
% 1.65/1.82              = (k4_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 1.65/1.82                 (k2_tops_1 @ X18 @ X17)))
% 1.65/1.82          | ~ (l1_pre_topc @ X18))),
% 1.65/1.82      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.65/1.82  thf('28', plain,
% 1.65/1.82      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.82        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.65/1.82            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['26', '27'])).
% 1.65/1.82  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('30', plain,
% 1.65/1.82      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.65/1.82  thf('31', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(t102_tops_1, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( l1_pre_topc @ A ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.82           ( ( v5_tops_1 @ B @ A ) =>
% 1.65/1.82             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 1.65/1.82               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.82  thf('32', plain,
% 1.65/1.82      (![X15 : $i, X16 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.65/1.82          | ((k2_tops_1 @ X16 @ (k1_tops_1 @ X16 @ X15))
% 1.65/1.82              = (k2_tops_1 @ X16 @ X15))
% 1.65/1.82          | ~ (v5_tops_1 @ X15 @ X16)
% 1.65/1.82          | ~ (l1_pre_topc @ X16))),
% 1.65/1.82      inference('cnf', [status(esa)], [t102_tops_1])).
% 1.65/1.82  thf('33', plain,
% 1.65/1.82      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.82        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 1.65/1.82        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.65/1.82            = (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['31', '32'])).
% 1.65/1.82  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('35', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('36', plain,
% 1.65/1.82      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.65/1.82         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.65/1.82      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.65/1.82  thf('37', plain,
% 1.65/1.82      (((sk_B)
% 1.65/1.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('demod', [status(thm)], ['28', '29', '30', '36'])).
% 1.65/1.82  thf('38', plain,
% 1.65/1.82      (((sk_B)
% 1.65/1.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('sup+', [status(thm)], ['25', '37'])).
% 1.65/1.82  thf('39', plain,
% 1.65/1.82      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.82      inference('demod', [status(thm)], ['20', '38'])).
% 1.65/1.82  thf(t31_subset_1, axiom,
% 1.65/1.82    (![A:$i,B:$i]:
% 1.65/1.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.82       ( ![C:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.82           ( ( r1_tarski @ B @ C ) <=>
% 1.65/1.82             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.82  thf('40', plain,
% 1.65/1.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.65/1.82          | ~ (r1_tarski @ (k3_subset_1 @ X4 @ X3) @ (k3_subset_1 @ X4 @ X5))
% 1.65/1.82          | (r1_tarski @ X5 @ X3)
% 1.65/1.82          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 1.65/1.82      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.65/1.82  thf('41', plain,
% 1.65/1.82      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.82        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.65/1.82        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['39', '40'])).
% 1.65/1.82  thf('42', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('demod', [status(thm)], ['10', '11'])).
% 1.65/1.82  thf('43', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('44', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.65/1.82      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.65/1.82  thf('45', plain, ($false), inference('demod', [status(thm)], ['7', '44'])).
% 1.65/1.82  
% 1.65/1.82  % SZS output end Refutation
% 1.65/1.82  
% 1.65/1.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
