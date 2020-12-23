%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N4iKV3Sl3x

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 162 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  628 (1958 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v5_tops_1 @ X13 @ X14 )
      | ( X13
        = ( k2_pre_topc @ X14 @ ( k1_tops_1 @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k4_subset_1 @ X8 @ X7 @ X9 )
        = ( k4_subset_1 @ X8 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf('31',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','31'])).

thf('33',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X22 @ ( k2_pre_topc @ X22 @ X21 ) ) @ ( k2_tops_1 @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['7','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N4iKV3Sl3x
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.20/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.37  % Solved by: fo/fo7.sh
% 1.20/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.37  % done 696 iterations in 0.907s
% 1.20/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.37  % SZS output start Refutation
% 1.20/1.37  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.20/1.37  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.20/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.20/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.37  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.20/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.20/1.37  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.20/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.37  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.20/1.37  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.20/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.37  thf(t103_tops_1, conjecture,
% 1.20/1.37    (![A:$i]:
% 1.20/1.37     ( ( l1_pre_topc @ A ) =>
% 1.20/1.37       ( ![B:$i]:
% 1.20/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.37           ( ( v5_tops_1 @ B @ A ) =>
% 1.20/1.37             ( r1_tarski @
% 1.20/1.37               ( k2_tops_1 @ A @ B ) @ 
% 1.20/1.37               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.20/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.37    (~( ![A:$i]:
% 1.20/1.37        ( ( l1_pre_topc @ A ) =>
% 1.20/1.37          ( ![B:$i]:
% 1.20/1.37            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.37              ( ( v5_tops_1 @ B @ A ) =>
% 1.20/1.37                ( r1_tarski @
% 1.20/1.37                  ( k2_tops_1 @ A @ B ) @ 
% 1.20/1.37                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.20/1.37    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.20/1.37  thf('0', plain,
% 1.20/1.37      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('1', plain,
% 1.20/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf(d7_tops_1, axiom,
% 1.20/1.37    (![A:$i]:
% 1.20/1.37     ( ( l1_pre_topc @ A ) =>
% 1.20/1.37       ( ![B:$i]:
% 1.20/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.37           ( ( v5_tops_1 @ B @ A ) <=>
% 1.20/1.37             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.20/1.37  thf('2', plain,
% 1.20/1.37      (![X13 : $i, X14 : $i]:
% 1.20/1.37         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.20/1.37          | ~ (v5_tops_1 @ X13 @ X14)
% 1.20/1.37          | ((X13) = (k2_pre_topc @ X14 @ (k1_tops_1 @ X14 @ X13)))
% 1.20/1.37          | ~ (l1_pre_topc @ X14))),
% 1.20/1.37      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.20/1.37  thf('3', plain,
% 1.20/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.37        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.20/1.37        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.20/1.37      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.37  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('6', plain,
% 1.20/1.37      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.20/1.37  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.20/1.37      inference('demod', [status(thm)], ['0', '6'])).
% 1.20/1.37  thf('8', plain,
% 1.20/1.37      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf(dt_k1_tops_1, axiom,
% 1.20/1.37    (![A:$i,B:$i]:
% 1.20/1.37     ( ( ( l1_pre_topc @ A ) & 
% 1.20/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.20/1.37       ( m1_subset_1 @
% 1.20/1.37         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.20/1.37  thf('9', plain,
% 1.20/1.37      (![X15 : $i, X16 : $i]:
% 1.20/1.37         (~ (l1_pre_topc @ X15)
% 1.20/1.37          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.20/1.37          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 1.20/1.37             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.20/1.37      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.20/1.37  thf('10', plain,
% 1.20/1.37      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.37        | ~ (l1_pre_topc @ sk_A))),
% 1.20/1.37      inference('sup-', [status(thm)], ['8', '9'])).
% 1.20/1.37  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('12', plain,
% 1.20/1.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['10', '11'])).
% 1.20/1.37  thf('13', plain,
% 1.20/1.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['10', '11'])).
% 1.20/1.37  thf(dt_k2_tops_1, axiom,
% 1.20/1.37    (![A:$i,B:$i]:
% 1.20/1.37     ( ( ( l1_pre_topc @ A ) & 
% 1.20/1.37         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.20/1.37       ( m1_subset_1 @
% 1.20/1.37         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.20/1.37  thf('14', plain,
% 1.20/1.37      (![X17 : $i, X18 : $i]:
% 1.20/1.37         (~ (l1_pre_topc @ X17)
% 1.20/1.37          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.20/1.37          | (m1_subset_1 @ (k2_tops_1 @ X17 @ X18) @ 
% 1.20/1.37             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 1.20/1.37      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.20/1.37  thf('15', plain,
% 1.20/1.37      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.37        | ~ (l1_pre_topc @ sk_A))),
% 1.20/1.37      inference('sup-', [status(thm)], ['13', '14'])).
% 1.20/1.37  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('17', plain,
% 1.20/1.37      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['15', '16'])).
% 1.20/1.37  thf(redefinition_k4_subset_1, axiom,
% 1.20/1.37    (![A:$i,B:$i,C:$i]:
% 1.20/1.37     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.20/1.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.20/1.37       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.20/1.37  thf('18', plain,
% 1.20/1.37      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.20/1.37         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.20/1.37          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 1.20/1.37          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 1.20/1.37      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.20/1.37  thf('19', plain,
% 1.20/1.37      (![X0 : $i]:
% 1.20/1.37         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.37            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0)
% 1.20/1.37            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37               X0))
% 1.20/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.20/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.20/1.37  thf('20', plain,
% 1.20/1.37      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.37         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37         (k1_tops_1 @ sk_A @ sk_B))
% 1.20/1.37         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('sup-', [status(thm)], ['12', '19'])).
% 1.20/1.37  thf('21', plain,
% 1.20/1.37      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['15', '16'])).
% 1.20/1.37  thf('22', plain,
% 1.20/1.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['10', '11'])).
% 1.20/1.37  thf(commutativity_k4_subset_1, axiom,
% 1.20/1.37    (![A:$i,B:$i,C:$i]:
% 1.20/1.37     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.20/1.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.20/1.37       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 1.20/1.37  thf('23', plain,
% 1.20/1.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.37         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.20/1.37          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 1.20/1.37          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k4_subset_1 @ X8 @ X9 @ X7)))),
% 1.20/1.37      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 1.20/1.37  thf('24', plain,
% 1.20/1.37      (![X0 : $i]:
% 1.20/1.37         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.20/1.37            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.20/1.37               (k1_tops_1 @ sk_A @ sk_B)))
% 1.20/1.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.20/1.37      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.37  thf('25', plain,
% 1.20/1.37      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.20/1.37         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.37            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('sup-', [status(thm)], ['21', '24'])).
% 1.20/1.37  thf('26', plain,
% 1.20/1.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['10', '11'])).
% 1.20/1.37  thf(t65_tops_1, axiom,
% 1.20/1.37    (![A:$i]:
% 1.20/1.37     ( ( l1_pre_topc @ A ) =>
% 1.20/1.37       ( ![B:$i]:
% 1.20/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.37           ( ( k2_pre_topc @ A @ B ) =
% 1.20/1.37             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.20/1.37  thf('27', plain,
% 1.20/1.37      (![X19 : $i, X20 : $i]:
% 1.20/1.37         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.20/1.37          | ((k2_pre_topc @ X20 @ X19)
% 1.20/1.37              = (k4_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 1.20/1.37                 (k2_tops_1 @ X20 @ X19)))
% 1.20/1.37          | ~ (l1_pre_topc @ X20))),
% 1.20/1.37      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.20/1.37  thf('28', plain,
% 1.20/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.37        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.20/1.37            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.37               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.20/1.37      inference('sup-', [status(thm)], ['26', '27'])).
% 1.20/1.37  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('30', plain,
% 1.20/1.37      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.20/1.37  thf('31', plain,
% 1.20/1.37      (((sk_B)
% 1.20/1.37         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.20/1.37      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.20/1.37  thf('32', plain,
% 1.20/1.37      (((sk_B)
% 1.20/1.37         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.37            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('demod', [status(thm)], ['25', '31'])).
% 1.20/1.37  thf('33', plain,
% 1.20/1.37      (((sk_B)
% 1.20/1.37         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.20/1.37            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('sup+', [status(thm)], ['20', '32'])).
% 1.20/1.37  thf(t7_xboole_1, axiom,
% 1.20/1.37    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.20/1.37  thf('34', plain,
% 1.20/1.37      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 1.20/1.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.20/1.37  thf('35', plain,
% 1.20/1.37      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.37      inference('demod', [status(thm)], ['10', '11'])).
% 1.20/1.37  thf(t72_tops_1, axiom,
% 1.20/1.37    (![A:$i]:
% 1.20/1.37     ( ( l1_pre_topc @ A ) =>
% 1.20/1.37       ( ![B:$i]:
% 1.20/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.37           ( r1_tarski @
% 1.20/1.37             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 1.20/1.37             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.20/1.37  thf('36', plain,
% 1.20/1.37      (![X21 : $i, X22 : $i]:
% 1.20/1.37         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.20/1.37          | (r1_tarski @ (k2_tops_1 @ X22 @ (k2_pre_topc @ X22 @ X21)) @ 
% 1.20/1.37             (k2_tops_1 @ X22 @ X21))
% 1.20/1.37          | ~ (l1_pre_topc @ X22))),
% 1.20/1.37      inference('cnf', [status(esa)], [t72_tops_1])).
% 1.20/1.37  thf('37', plain,
% 1.20/1.37      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.37        | (r1_tarski @ 
% 1.20/1.37           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.20/1.37           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.20/1.37      inference('sup-', [status(thm)], ['35', '36'])).
% 1.20/1.37  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.37  thf('39', plain,
% 1.20/1.37      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.20/1.37  thf('40', plain,
% 1.20/1.37      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.20/1.37      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.20/1.37  thf(t1_xboole_1, axiom,
% 1.20/1.37    (![A:$i,B:$i,C:$i]:
% 1.20/1.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.20/1.37       ( r1_tarski @ A @ C ) ))).
% 1.20/1.37  thf('41', plain,
% 1.20/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.37         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.37          | ~ (r1_tarski @ X1 @ X2)
% 1.20/1.37          | (r1_tarski @ X0 @ X2))),
% 1.20/1.37      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.20/1.37  thf('42', plain,
% 1.20/1.37      (![X0 : $i]:
% 1.20/1.37         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.20/1.37          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.20/1.37      inference('sup-', [status(thm)], ['40', '41'])).
% 1.20/1.37  thf('43', plain,
% 1.20/1.37      (![X0 : $i]:
% 1.20/1.37         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.37          (k2_xboole_0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.20/1.37      inference('sup-', [status(thm)], ['34', '42'])).
% 1.20/1.37  thf('44', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.20/1.37      inference('sup+', [status(thm)], ['33', '43'])).
% 1.20/1.37  thf('45', plain, ($false), inference('demod', [status(thm)], ['7', '44'])).
% 1.20/1.37  
% 1.20/1.37  % SZS output end Refutation
% 1.20/1.37  
% 1.20/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
