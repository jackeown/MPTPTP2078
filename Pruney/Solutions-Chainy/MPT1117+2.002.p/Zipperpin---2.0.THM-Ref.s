%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2cUPNC9U6v

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:17 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 ( 685 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( sk_D @ X9 @ X7 @ X8 ) )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X1 @ sk_B ) @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_B @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X9 @ ( sk_D @ X9 @ X7 @ X8 ) )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2cUPNC9U6v
% 0.15/0.38  % Computer   : n002.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 11:02:37 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.57  % Solved by: fo/fo7.sh
% 0.25/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.57  % done 78 iterations in 0.076s
% 0.25/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.57  % SZS output start Refutation
% 0.25/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.25/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.25/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.25/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.57  thf(t48_pre_topc, conjecture,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( l1_pre_topc @ A ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.57           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.25/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.57    (~( ![A:$i]:
% 0.25/0.57        ( ( l1_pre_topc @ A ) =>
% 0.25/0.57          ( ![B:$i]:
% 0.25/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.57              ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ) )),
% 0.25/0.57    inference('cnf.neg', [status(esa)], [t48_pre_topc])).
% 0.25/0.57  thf('0', plain, (~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(d3_tarski, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.57  thf('1', plain,
% 0.25/0.57      (![X1 : $i, X3 : $i]:
% 0.25/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('2', plain,
% 0.25/0.57      (![X1 : $i, X3 : $i]:
% 0.25/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('3', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t3_subset, axiom,
% 0.25/0.57    (![A:$i,B:$i]:
% 0.25/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.57  thf('4', plain,
% 0.25/0.57      (![X4 : $i, X5 : $i]:
% 0.25/0.57         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.25/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.25/0.57  thf('5', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.25/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.57  thf('6', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.57          | (r2_hidden @ X0 @ X2)
% 0.25/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('7', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.25/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.25/0.57  thf('8', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['2', '7'])).
% 0.25/0.57  thf('9', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf(t45_pre_topc, axiom,
% 0.25/0.57    (![A:$i]:
% 0.25/0.57     ( ( l1_pre_topc @ A ) =>
% 0.25/0.57       ( ![B:$i]:
% 0.25/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.57           ( ![C:$i]:
% 0.25/0.57             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.57               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.25/0.57                 ( ![D:$i]:
% 0.25/0.57                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.57                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.25/0.57                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.57  thf('10', plain,
% 0.25/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.25/0.57         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.25/0.57          | (r1_tarski @ X7 @ (sk_D @ X9 @ X7 @ X8))
% 0.25/0.57          | (r2_hidden @ X9 @ (k2_pre_topc @ X8 @ X7))
% 0.25/0.57          | ~ (r2_hidden @ X9 @ (u1_struct_0 @ X8))
% 0.25/0.57          | ~ (l1_pre_topc @ X8))),
% 0.25/0.57      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.25/0.57  thf('11', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (l1_pre_topc @ sk_A)
% 0.25/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | (r1_tarski @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.57  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('13', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | (r1_tarski @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.25/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.25/0.57  thf('14', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r1_tarski @ sk_B @ (sk_D @ (sk_C @ X0 @ sk_B) @ sk_B @ sk_A))
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['8', '13'])).
% 0.25/0.57  thf('15', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.57          | (r2_hidden @ X0 @ X2)
% 0.25/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('16', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]:
% 0.25/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | (r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r2_hidden @ X1 @ (sk_D @ (sk_C @ X0 @ sk_B) @ sk_B @ sk_A))
% 0.25/0.57          | ~ (r2_hidden @ X1 @ sk_B))),
% 0.25/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.57  thf('17', plain,
% 0.25/0.57      (![X0 : $i, X1 : $i]:
% 0.25/0.57         ((r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 0.25/0.57             (sk_D @ (sk_C @ X1 @ sk_B) @ sk_B @ sk_A))
% 0.25/0.57          | (r1_tarski @ sk_B @ X1)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X1 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['1', '16'])).
% 0.25/0.57  thf('18', plain,
% 0.25/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('19', plain,
% 0.25/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.25/0.57         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.25/0.57          | ~ (r2_hidden @ X9 @ (sk_D @ X9 @ X7 @ X8))
% 0.25/0.57          | (r2_hidden @ X9 @ (k2_pre_topc @ X8 @ X7))
% 0.25/0.57          | ~ (r2_hidden @ X9 @ (u1_struct_0 @ X8))
% 0.25/0.57          | ~ (l1_pre_topc @ X8))),
% 0.25/0.57      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.25/0.57  thf('20', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (l1_pre_topc @ sk_A)
% 0.25/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.57  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.57  thf('22', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.25/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.25/0.57  thf('23', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | (r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['17', '22'])).
% 0.25/0.57  thf('24', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         (~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.25/0.57          | (r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.25/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.25/0.57  thf('25', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r1_tarski @ sk_B @ X0)
% 0.25/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['2', '7'])).
% 0.25/0.57  thf('26', plain,
% 0.25/0.57      (![X0 : $i]:
% 0.25/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57          | (r1_tarski @ sk_B @ X0))),
% 0.25/0.57      inference('clc', [status(thm)], ['24', '25'])).
% 0.25/0.57  thf('27', plain,
% 0.25/0.57      (![X1 : $i, X3 : $i]:
% 0.25/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.25/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.57  thf('28', plain,
% 0.25/0.57      (((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.25/0.57        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.25/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.25/0.57  thf('29', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.25/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.25/0.57  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.25/0.57  
% 0.25/0.57  % SZS output end Refutation
% 0.25/0.57  
% 0.25/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
