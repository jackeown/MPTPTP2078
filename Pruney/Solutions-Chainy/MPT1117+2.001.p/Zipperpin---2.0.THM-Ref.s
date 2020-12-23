%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G1ibgGH8Xi

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  403 ( 653 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t48_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X1 @ sk_B ) @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_B @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X9 @ ( sk_D @ X9 @ X7 @ X8 ) )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G1ibgGH8Xi
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 37 iterations in 0.034s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(t48_pre_topc, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( l1_pre_topc @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48              ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t48_pre_topc])).
% 0.21/0.48  thf('0', plain, (~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(l3_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.48          | (r2_hidden @ X4 @ X6)
% 0.21/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t45_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.21/0.48                 ( ![D:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.21/0.48                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | (r1_tarski @ X7 @ (sk_D @ X9 @ X7 @ X8))
% 0.21/0.48          | (r2_hidden @ X9 @ (k2_pre_topc @ X8 @ X7))
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | (r1_tarski @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | (r1_tarski @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r1_tarski @ sk_B @ (sk_D @ (sk_C @ X0 @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.48          | (r2_hidden @ X0 @ X2)
% 0.21/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | (r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ X1 @ (sk_D @ (sk_C @ X0 @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.21/0.48             (sk_D @ (sk_C @ X1 @ sk_B) @ sk_B @ sk_A))
% 0.21/0.48          | (r1_tarski @ sk_B @ X1)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X1 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (sk_D @ X9 @ X7 @ X8))
% 0.21/0.48          | (r2_hidden @ X9 @ (k2_pre_topc @ X8 @ X7))
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | (r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.48          | (r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ sk_B @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48          | (r1_tarski @ sk_B @ X0))),
% 0.21/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.48        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.21/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.48  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
