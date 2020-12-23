%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YlRj4qikEy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  480 ( 649 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( sk_C @ X14 @ X15 ) @ X14 )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('18',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X15 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X17 )
       != ( sk_C @ X14 @ X15 ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X6 @ X5 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('34',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YlRj4qikEy
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:30:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 114 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.53  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf(l13_xboole_0, axiom,
% 0.21/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.53  thf(t4_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf(d6_tex_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.53             ( ![C:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.53                      ( ![D:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @
% 0.21/0.53                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.53                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.53                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.53          | (r1_tarski @ (sk_C @ X14 @ X15) @ X14)
% 0.21/0.53          | (v2_tex_2 @ X14 @ X15)
% 0.21/0.53          | ~ (l1_pre_topc @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.53          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (sk_C @ X0 @ X1) @ k1_xboole_0)
% 0.21/0.53          | ~ (v1_xboole_0 @ X0)
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X1)
% 0.21/0.53          | ~ (l1_pre_topc @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('6', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (v1_xboole_0 @ X1)
% 0.21/0.53          | ((sk_C @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(cc2_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.53          | (v4_pre_topc @ X12 @ X13)
% 0.21/0.53          | ~ (v1_xboole_0 @ X12)
% 0.21/0.53          | ~ (l1_pre_topc @ X13)
% 0.21/0.53          | ~ (v2_pre_topc @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ X1)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_xboole_0 @ X1)
% 0.21/0.53          | (v4_pre_topc @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v4_pre_topc @ X1 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.53          | ~ (v4_pre_topc @ X17 @ X15)
% 0.21/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ X14 @ X17)
% 0.21/0.53              != (sk_C @ X14 @ X15))
% 0.21/0.53          | (v2_tex_2 @ X14 @ X15)
% 0.21/0.53          | ~ (l1_pre_topc @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.21/0.53              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.53          | ~ (v4_pre_topc @ X1 @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.53              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.53  thf(idempotence_k9_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (((k9_subset_1 @ X6 @ X5 @ X5) = (X5))
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.53      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.21/0.53          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.53          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '25'])).
% 0.21/0.54  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (sk_C @ X0 @ X1))
% 0.21/0.54          | ~ (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X1)
% 0.21/0.54          | ~ (l1_pre_topc @ X1)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_xboole_0 @ X1)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | ~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v2_pre_topc @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ X0)
% 0.21/0.54          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf(t35_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.21/0.54  thf('34', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '39'])).
% 0.21/0.54  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('44', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.21/0.54      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.21/0.54  thf('45', plain, ($false), inference('sup-', [status(thm)], ['0', '44'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
