%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQyRJLlr4H

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:50 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 134 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  543 (1547 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v5_tops_1 @ X11 @ X12 )
      | ( X11
        = ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) )
      | ( ( k4_subset_1 @ X9 @ X8 @ X10 )
        = ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( k2_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('26',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X20 @ ( k2_pre_topc @ X20 @ X19 ) ) @ ( k2_tops_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('36',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['7','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQyRJLlr4H
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.21/1.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.21/1.40  % Solved by: fo/fo7.sh
% 1.21/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.40  % done 563 iterations in 0.939s
% 1.21/1.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.21/1.40  % SZS output start Refutation
% 1.21/1.40  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.21/1.40  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.21/1.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.40  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.21/1.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.21/1.40  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.21/1.40  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.21/1.40  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.21/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.40  thf(t103_tops_1, conjecture,
% 1.21/1.40    (![A:$i]:
% 1.21/1.40     ( ( l1_pre_topc @ A ) =>
% 1.21/1.40       ( ![B:$i]:
% 1.21/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.40           ( ( v5_tops_1 @ B @ A ) =>
% 1.21/1.40             ( r1_tarski @
% 1.21/1.40               ( k2_tops_1 @ A @ B ) @ 
% 1.21/1.40               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.21/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.40    (~( ![A:$i]:
% 1.21/1.40        ( ( l1_pre_topc @ A ) =>
% 1.21/1.40          ( ![B:$i]:
% 1.21/1.40            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.40              ( ( v5_tops_1 @ B @ A ) =>
% 1.21/1.40                ( r1_tarski @
% 1.21/1.40                  ( k2_tops_1 @ A @ B ) @ 
% 1.21/1.40                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.21/1.40    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.21/1.40  thf('0', plain,
% 1.21/1.40      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('1', plain,
% 1.21/1.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf(d7_tops_1, axiom,
% 1.21/1.40    (![A:$i]:
% 1.21/1.40     ( ( l1_pre_topc @ A ) =>
% 1.21/1.40       ( ![B:$i]:
% 1.21/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.40           ( ( v5_tops_1 @ B @ A ) <=>
% 1.21/1.40             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.21/1.40  thf('2', plain,
% 1.21/1.40      (![X11 : $i, X12 : $i]:
% 1.21/1.40         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.21/1.40          | ~ (v5_tops_1 @ X11 @ X12)
% 1.21/1.40          | ((X11) = (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 1.21/1.40          | ~ (l1_pre_topc @ X12))),
% 1.21/1.40      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.21/1.40  thf('3', plain,
% 1.21/1.40      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.40        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.21/1.40        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.21/1.40      inference('sup-', [status(thm)], ['1', '2'])).
% 1.21/1.40  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('6', plain,
% 1.21/1.40      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.21/1.40      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.21/1.40  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.21/1.40      inference('demod', [status(thm)], ['0', '6'])).
% 1.21/1.40  thf('8', plain,
% 1.21/1.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf(dt_k1_tops_1, axiom,
% 1.21/1.40    (![A:$i,B:$i]:
% 1.21/1.40     ( ( ( l1_pre_topc @ A ) & 
% 1.21/1.40         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.21/1.40       ( m1_subset_1 @
% 1.21/1.40         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.21/1.40  thf('9', plain,
% 1.21/1.40      (![X13 : $i, X14 : $i]:
% 1.21/1.40         (~ (l1_pre_topc @ X13)
% 1.21/1.40          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.21/1.40          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 1.21/1.40             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 1.21/1.40      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.21/1.40  thf('10', plain,
% 1.21/1.40      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.21/1.40        | ~ (l1_pre_topc @ sk_A))),
% 1.21/1.40      inference('sup-', [status(thm)], ['8', '9'])).
% 1.21/1.40  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('12', plain,
% 1.21/1.40      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('demod', [status(thm)], ['10', '11'])).
% 1.21/1.40  thf(dt_k2_tops_1, axiom,
% 1.21/1.40    (![A:$i,B:$i]:
% 1.21/1.40     ( ( ( l1_pre_topc @ A ) & 
% 1.21/1.40         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.21/1.40       ( m1_subset_1 @
% 1.21/1.40         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.21/1.40  thf('13', plain,
% 1.21/1.40      (![X15 : $i, X16 : $i]:
% 1.21/1.40         (~ (l1_pre_topc @ X15)
% 1.21/1.40          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.21/1.40          | (m1_subset_1 @ (k2_tops_1 @ X15 @ X16) @ 
% 1.21/1.40             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.21/1.40      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.21/1.40  thf('14', plain,
% 1.21/1.40      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.21/1.40         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.21/1.40        | ~ (l1_pre_topc @ sk_A))),
% 1.21/1.40      inference('sup-', [status(thm)], ['12', '13'])).
% 1.21/1.40  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('16', plain,
% 1.21/1.40      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.21/1.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('demod', [status(thm)], ['14', '15'])).
% 1.21/1.40  thf('17', plain,
% 1.21/1.40      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('demod', [status(thm)], ['10', '11'])).
% 1.21/1.40  thf(redefinition_k4_subset_1, axiom,
% 1.21/1.40    (![A:$i,B:$i,C:$i]:
% 1.21/1.40     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.21/1.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.40       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.21/1.40  thf('18', plain,
% 1.21/1.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.21/1.40         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.21/1.40          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9))
% 1.21/1.40          | ((k4_subset_1 @ X9 @ X8 @ X10) = (k2_xboole_0 @ X8 @ X10)))),
% 1.21/1.40      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.21/1.40  thf('19', plain,
% 1.21/1.40      (![X0 : $i]:
% 1.21/1.40         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.21/1.40            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 1.21/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.21/1.40      inference('sup-', [status(thm)], ['17', '18'])).
% 1.21/1.40  thf('20', plain,
% 1.21/1.40      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.21/1.40         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.21/1.40      inference('sup-', [status(thm)], ['16', '19'])).
% 1.21/1.40  thf('21', plain,
% 1.21/1.40      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('demod', [status(thm)], ['10', '11'])).
% 1.21/1.40  thf(t65_tops_1, axiom,
% 1.21/1.40    (![A:$i]:
% 1.21/1.40     ( ( l1_pre_topc @ A ) =>
% 1.21/1.40       ( ![B:$i]:
% 1.21/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.40           ( ( k2_pre_topc @ A @ B ) =
% 1.21/1.40             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.21/1.40  thf('22', plain,
% 1.21/1.40      (![X17 : $i, X18 : $i]:
% 1.21/1.40         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.21/1.40          | ((k2_pre_topc @ X18 @ X17)
% 1.21/1.40              = (k4_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 1.21/1.40                 (k2_tops_1 @ X18 @ X17)))
% 1.21/1.40          | ~ (l1_pre_topc @ X18))),
% 1.21/1.40      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.21/1.40  thf('23', plain,
% 1.21/1.40      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.40        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.21/1.40            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.21/1.40               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.21/1.40      inference('sup-', [status(thm)], ['21', '22'])).
% 1.21/1.40  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('25', plain,
% 1.21/1.40      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.21/1.40      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.21/1.40  thf('26', plain,
% 1.21/1.40      (((sk_B)
% 1.21/1.40         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.21/1.40      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.21/1.40  thf('27', plain,
% 1.21/1.40      (((sk_B)
% 1.21/1.40         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.21/1.40      inference('sup+', [status(thm)], ['20', '26'])).
% 1.21/1.40  thf(t36_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.21/1.40  thf('28', plain,
% 1.21/1.40      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 1.21/1.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.21/1.40  thf(t44_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i,C:$i]:
% 1.21/1.40     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.21/1.40       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.21/1.40  thf('29', plain,
% 1.21/1.40      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.21/1.40         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 1.21/1.40          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 1.21/1.40      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.21/1.40  thf('30', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.21/1.40      inference('sup-', [status(thm)], ['28', '29'])).
% 1.21/1.40  thf('31', plain,
% 1.21/1.40      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.21/1.40      inference('demod', [status(thm)], ['10', '11'])).
% 1.21/1.40  thf(t72_tops_1, axiom,
% 1.21/1.40    (![A:$i]:
% 1.21/1.40     ( ( l1_pre_topc @ A ) =>
% 1.21/1.40       ( ![B:$i]:
% 1.21/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.21/1.40           ( r1_tarski @
% 1.21/1.40             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 1.21/1.40             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.21/1.40  thf('32', plain,
% 1.21/1.40      (![X19 : $i, X20 : $i]:
% 1.21/1.40         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.21/1.40          | (r1_tarski @ (k2_tops_1 @ X20 @ (k2_pre_topc @ X20 @ X19)) @ 
% 1.21/1.40             (k2_tops_1 @ X20 @ X19))
% 1.21/1.40          | ~ (l1_pre_topc @ X20))),
% 1.21/1.40      inference('cnf', [status(esa)], [t72_tops_1])).
% 1.21/1.40  thf('33', plain,
% 1.21/1.40      ((~ (l1_pre_topc @ sk_A)
% 1.21/1.40        | (r1_tarski @ 
% 1.21/1.40           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.21/1.40           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.21/1.40      inference('sup-', [status(thm)], ['31', '32'])).
% 1.21/1.40  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf('35', plain,
% 1.21/1.40      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.21/1.40      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.21/1.40  thf('36', plain,
% 1.21/1.40      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.21/1.40      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.21/1.40  thf(t1_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i,C:$i]:
% 1.21/1.40     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.21/1.40       ( r1_tarski @ A @ C ) ))).
% 1.21/1.40  thf('37', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.40         (~ (r1_tarski @ X0 @ X1)
% 1.21/1.40          | ~ (r1_tarski @ X1 @ X2)
% 1.21/1.40          | (r1_tarski @ X0 @ X2))),
% 1.21/1.40      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.21/1.40  thf('38', plain,
% 1.21/1.40      (![X0 : $i]:
% 1.21/1.40         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.21/1.40          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.21/1.40      inference('sup-', [status(thm)], ['36', '37'])).
% 1.21/1.40  thf('39', plain,
% 1.21/1.40      (![X0 : $i]:
% 1.21/1.40         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.21/1.40          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.21/1.40      inference('sup-', [status(thm)], ['30', '38'])).
% 1.21/1.40  thf('40', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.21/1.40      inference('sup+', [status(thm)], ['27', '39'])).
% 1.21/1.40  thf('41', plain, ($false), inference('demod', [status(thm)], ['7', '40'])).
% 1.21/1.40  
% 1.21/1.40  % SZS output end Refutation
% 1.21/1.40  
% 1.21/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
