%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uaFyvcutIs

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  286 ( 629 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t13_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
          <=> ( v1_finset_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
            <=> ( v1_finset_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tops_2])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
           => ( v1_finset_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_finset_1 @ X4 )
      | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_tops_2])).

thf('6',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_finset_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_finset_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_finset_1 @ sk_B )
   <= ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ~ ( v1_finset_1 @ sk_B )
   <= ~ ( v1_finset_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( v1_finset_1 @ sk_B )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ( v1_finset_1 @ sk_B )
   <= ( v1_finset_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('16',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_finset_1 @ X4 )
      | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_tops_2])).

thf('18',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('22',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,
    ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v1_finset_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,
    ( ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uaFyvcutIs
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 20 iterations in 0.012s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.19/0.46  thf(t13_tops_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @
% 0.19/0.46             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46           ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.19/0.46             ( v1_finset_1 @ B ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( l1_struct_0 @ A ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( m1_subset_1 @
% 0.19/0.46                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46              ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.19/0.46                ( v1_finset_1 @ B ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t13_tops_2])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((~ (v1_finset_1 @ sk_B)
% 0.19/0.46        | ~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (~ ((v1_finset_1 @ sk_B)) | 
% 0.19/0.46       ~ ((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (((v1_finset_1 @ sk_B)
% 0.19/0.46        | (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.46         <= (((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.46      inference('split', [status(esa)], ['2'])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ 
% 0.19/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(l13_tops_2, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_struct_0 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @
% 0.19/0.46             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46           ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) ) =>
% 0.19/0.46             ( v1_finset_1 @ B ) ) ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X4 @ 
% 0.19/0.46             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.19/0.46          | (v1_finset_1 @ X4)
% 0.19/0.46          | ~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ X5) @ X4))
% 0.19/0.46          | ~ (l1_struct_0 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [l13_tops_2])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.46        | ~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.46        | (v1_finset_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      ((~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.46        | (v1_finset_1 @ sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (((v1_finset_1 @ sk_B))
% 0.19/0.46         <= (((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '8'])).
% 0.19/0.46  thf('10', plain, ((~ (v1_finset_1 @ sk_B)) <= (~ ((v1_finset_1 @ sk_B)))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (((v1_finset_1 @ sk_B)) | 
% 0.19/0.46       ~ ((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (((v1_finset_1 @ sk_B)) | 
% 0.19/0.46       ((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('split', [status(esa)], ['2'])).
% 0.19/0.46  thf('13', plain, (((v1_finset_1 @ sk_B)) <= (((v1_finset_1 @ sk_B)))),
% 0.19/0.46      inference('split', [status(esa)], ['2'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ 
% 0.19/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_k7_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46       ( m1_subset_1 @
% 0.19/0.46         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.19/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X4 @ 
% 0.19/0.46             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.19/0.46          | (v1_finset_1 @ X4)
% 0.19/0.46          | ~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ X5) @ X4))
% 0.19/0.46          | ~ (l1_struct_0 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [l13_tops_2])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.46        | ~ (v1_finset_1 @ 
% 0.19/0.46             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.46              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.46        | (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.46  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ 
% 0.19/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(involutiveness_k7_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.19/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.19/0.46      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.46         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      ((~ (v1_finset_1 @ sk_B)
% 0.19/0.46        | (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '19', '22'])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.46         <= (((v1_finset_1 @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['13', '23'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      ((~ (v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.46         <= (~ ((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (~ ((v1_finset_1 @ sk_B)) | 
% 0.19/0.46       ((v1_finset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf('27', plain, ($false),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['1', '11', '12', '26'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
