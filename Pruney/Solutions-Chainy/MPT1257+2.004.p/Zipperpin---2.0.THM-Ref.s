%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rrBXrsB0gj

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:18 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  668 (1254 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t73_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X6 @ ( k4_subset_1 @ X6 @ X7 @ X5 ) ) @ ( k3_subset_1 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k4_subset_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ X17 )
        = ( k2_tops_1 @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','27','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ( r1_xboole_0 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rrBXrsB0gj
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.65/1.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.83  % Solved by: fo/fo7.sh
% 1.65/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.83  % done 641 iterations in 1.376s
% 1.65/1.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.83  % SZS output start Refutation
% 1.65/1.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.65/1.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.65/1.83  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.65/1.83  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.83  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.83  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.65/1.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.65/1.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.83  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.65/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.83  thf(t73_tops_1, conjecture,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( l1_pre_topc @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.83           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.83    (~( ![A:$i]:
% 1.65/1.83        ( ( l1_pre_topc @ A ) =>
% 1.65/1.83          ( ![B:$i]:
% 1.65/1.83            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.83              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 1.65/1.83    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 1.65/1.83  thf('0', plain,
% 1.65/1.83      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('1', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(dt_k2_tops_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ( l1_pre_topc @ A ) & 
% 1.65/1.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.83       ( m1_subset_1 @
% 1.65/1.83         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.83  thf('2', plain,
% 1.65/1.83      (![X15 : $i, X16 : $i]:
% 1.65/1.83         (~ (l1_pre_topc @ X15)
% 1.65/1.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.65/1.83          | (m1_subset_1 @ (k2_tops_1 @ X15 @ X16) @ 
% 1.65/1.83             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.65/1.83      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.65/1.83  thf('3', plain,
% 1.65/1.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.83        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.83  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('5', plain,
% 1.65/1.83      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['3', '4'])).
% 1.65/1.83  thf('6', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(dt_k3_subset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.83       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.65/1.83  thf('7', plain,
% 1.65/1.83      (![X3 : $i, X4 : $i]:
% 1.65/1.83         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 1.65/1.83          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 1.65/1.83      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.65/1.83  thf('8', plain,
% 1.65/1.83      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['6', '7'])).
% 1.65/1.83  thf(t41_subset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.83       ( ![C:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.83           ( r1_tarski @
% 1.65/1.83             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.65/1.83             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.65/1.83  thf('9', plain,
% 1.65/1.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.65/1.83          | (r1_tarski @ (k3_subset_1 @ X6 @ (k4_subset_1 @ X6 @ X7 @ X5)) @ 
% 1.65/1.83             (k3_subset_1 @ X6 @ X7))
% 1.65/1.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t41_subset_1])).
% 1.65/1.83  thf('10', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.83          | (r1_tarski @ 
% 1.65/1.83             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.65/1.83               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 1.65/1.83             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['8', '9'])).
% 1.65/1.83  thf('11', plain,
% 1.65/1.83      ((r1_tarski @ 
% 1.65/1.83        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 1.65/1.83        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['5', '10'])).
% 1.65/1.83  thf('12', plain,
% 1.65/1.83      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['3', '4'])).
% 1.65/1.83  thf('13', plain,
% 1.65/1.83      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['6', '7'])).
% 1.65/1.83  thf(commutativity_k4_subset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.65/1.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.65/1.83       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 1.65/1.83  thf('14', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.83          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 1.65/1.83          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k4_subset_1 @ X1 @ X2 @ X0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 1.65/1.83  thf('15', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 1.65/1.83            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.65/1.83               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.65/1.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('16', plain,
% 1.65/1.83      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.83         (k2_tops_1 @ sk_A @ sk_B))
% 1.65/1.83         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['12', '15'])).
% 1.65/1.83  thf('17', plain,
% 1.65/1.83      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['6', '7'])).
% 1.65/1.83  thf(t65_tops_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( l1_pre_topc @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.83           ( ( k2_pre_topc @ A @ B ) =
% 1.65/1.83             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.65/1.83  thf('18', plain,
% 1.65/1.83      (![X19 : $i, X20 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.65/1.83          | ((k2_pre_topc @ X20 @ X19)
% 1.65/1.83              = (k4_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 1.65/1.83                 (k2_tops_1 @ X20 @ X19)))
% 1.65/1.83          | ~ (l1_pre_topc @ X20))),
% 1.65/1.83      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.65/1.83  thf('19', plain,
% 1.65/1.83      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.83        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.65/1.83            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.83               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['17', '18'])).
% 1.65/1.83  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('21', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(t62_tops_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( l1_pre_topc @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.83           ( ( k2_tops_1 @ A @ B ) =
% 1.65/1.83             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.65/1.83  thf('22', plain,
% 1.65/1.83      (![X17 : $i, X18 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.65/1.83          | ((k2_tops_1 @ X18 @ X17)
% 1.65/1.83              = (k2_tops_1 @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17)))
% 1.65/1.83          | ~ (l1_pre_topc @ X18))),
% 1.65/1.83      inference('cnf', [status(esa)], [t62_tops_1])).
% 1.65/1.83  thf('23', plain,
% 1.65/1.83      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.83        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.83            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['21', '22'])).
% 1.65/1.83  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('25', plain,
% 1.65/1.83      (((k2_tops_1 @ sk_A @ sk_B)
% 1.65/1.83         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.65/1.83      inference('demod', [status(thm)], ['23', '24'])).
% 1.65/1.83  thf('26', plain,
% 1.65/1.83      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.65/1.83         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.65/1.83            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('demod', [status(thm)], ['19', '20', '25'])).
% 1.65/1.83  thf('27', plain,
% 1.65/1.83      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.65/1.83         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['16', '26'])).
% 1.65/1.83  thf('28', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(d1_tops_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( l1_pre_topc @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.83           ( ( k1_tops_1 @ A @ B ) =
% 1.65/1.83             ( k3_subset_1 @
% 1.65/1.83               ( u1_struct_0 @ A ) @ 
% 1.65/1.83               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.65/1.83  thf('29', plain,
% 1.65/1.83      (![X11 : $i, X12 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.65/1.83          | ((k1_tops_1 @ X12 @ X11)
% 1.65/1.83              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.65/1.83                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 1.65/1.83          | ~ (l1_pre_topc @ X12))),
% 1.65/1.83      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.65/1.83  thf('30', plain,
% 1.65/1.83      ((~ (l1_pre_topc @ sk_A)
% 1.65/1.83        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.65/1.83            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83               (k2_pre_topc @ sk_A @ 
% 1.65/1.83                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['28', '29'])).
% 1.65/1.83  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('32', plain,
% 1.65/1.83      (((k1_tops_1 @ sk_A @ sk_B)
% 1.65/1.83         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.65/1.83      inference('demod', [status(thm)], ['30', '31'])).
% 1.65/1.83  thf('33', plain,
% 1.65/1.83      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.65/1.83      inference('demod', [status(thm)], ['11', '27', '32'])).
% 1.65/1.83  thf('34', plain,
% 1.65/1.83      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['3', '4'])).
% 1.65/1.83  thf(t43_subset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.83       ( ![C:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.83           ( ( r1_xboole_0 @ B @ C ) <=>
% 1.65/1.83             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.65/1.83  thf('35', plain,
% 1.65/1.83      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.65/1.83          | ~ (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 1.65/1.83          | (r1_xboole_0 @ X10 @ X8)
% 1.65/1.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t43_subset_1])).
% 1.65/1.83  thf('36', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.83          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 1.65/1.83          | ~ (r1_tarski @ X0 @ 
% 1.65/1.83               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['34', '35'])).
% 1.65/1.83  thf('37', plain,
% 1.65/1.83      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.65/1.83        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['33', '36'])).
% 1.65/1.83  thf('38', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(dt_k1_tops_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ( l1_pre_topc @ A ) & 
% 1.65/1.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.65/1.83       ( m1_subset_1 @
% 1.65/1.83         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.83  thf('39', plain,
% 1.65/1.83      (![X13 : $i, X14 : $i]:
% 1.65/1.83         (~ (l1_pre_topc @ X13)
% 1.65/1.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.65/1.83          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 1.65/1.83             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 1.65/1.83      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.65/1.83  thf('40', plain,
% 1.65/1.83      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.65/1.83        | ~ (l1_pre_topc @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['38', '39'])).
% 1.65/1.83  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('42', plain,
% 1.65/1.83      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['40', '41'])).
% 1.65/1.83  thf('43', plain,
% 1.65/1.83      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '42'])).
% 1.65/1.83  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 1.65/1.83  
% 1.65/1.83  % SZS output end Refutation
% 1.65/1.83  
% 1.65/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
