%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tj398a0pEA

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  371 ( 989 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t18_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( v1_tops_2 @ C @ A ) )
                 => ( v1_tops_2 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v1_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['28','29'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['20','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['6','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tj398a0pEA
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 117 iterations in 0.073s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(t18_tops_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_pre_topc @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @
% 0.22/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_subset_1 @
% 0.22/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.22/0.53                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( l1_pre_topc @ A ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( m1_subset_1 @
% 0.22/0.53                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( m1_subset_1 @
% 0.22/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53                  ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.22/0.53                    ( v1_tops_2 @ B @ A ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t18_tops_2])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ 
% 0.22/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d1_tops_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_pre_topc @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @
% 0.22/0.53             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.53           ( ( v1_tops_2 @ B @ A ) <=>
% 0.22/0.53             ( ![C:$i]:
% 0.22/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.53                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X8 @ 
% 0.22/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.22/0.53          | ~ (v3_pre_topc @ (sk_C @ X8 @ X9) @ X9)
% 0.22/0.53          | (v1_tops_2 @ X8 @ X9)
% 0.22/0.53          | ~ (l1_pre_topc @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (v1_tops_2 @ sk_B @ sk_A)
% 0.22/0.53        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (((v1_tops_2 @ sk_B @ sk_A)
% 0.22/0.53        | ~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('5', plain, (~ (v1_tops_2 @ sk_B @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('6', plain, (~ (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.53      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ 
% 0.22/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X8 @ 
% 0.22/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.22/0.53          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.22/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.53          | (v1_tops_2 @ X8 @ X9)
% 0.22/0.53          | ~ (l1_pre_topc @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (v1_tops_2 @ sk_B @ sk_A)
% 0.22/0.53        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (((v1_tops_2 @ sk_B @ sk_A)
% 0.22/0.53        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf('12', plain, (~ (v1_tops_2 @ sk_B @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.22/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X8 @ 
% 0.22/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.22/0.53          | ~ (v1_tops_2 @ X8 @ X9)
% 0.22/0.53          | ~ (r2_hidden @ X10 @ X8)
% 0.22/0.53          | (v3_pre_topc @ X10 @ X9)
% 0.22/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.53          | ~ (l1_pre_topc @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.53          | (v3_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.22/0.53          | ~ (v1_tops_2 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.53  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('18', plain, ((v1_tops_2 @ sk_C_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.53          | (v3_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1)
% 0.22/0.53        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '19'])).
% 0.22/0.53  thf('21', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t12_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i]:
% 0.22/0.53         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.53  thf('23', plain, (((k2_xboole_0 @ sk_B @ sk_C_1) = (sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ 
% 0.22/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X8 @ 
% 0.22/0.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.22/0.53          | (r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 0.22/0.53          | (v1_tops_2 @ X8 @ X9)
% 0.22/0.53          | ~ (l1_pre_topc @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.53        | (v1_tops_2 @ sk_B @ sk_A)
% 0.22/0.53        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (((v1_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.53  thf('29', plain, (~ (v1_tops_2 @ sk_B @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('30', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.22/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf(d3_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.22/0.53       ( ![D:$i]:
% 0.22/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.53           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X3)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.22/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '32'])).
% 0.22/0.53  thf('34', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1)),
% 0.22/0.53      inference('sup+', [status(thm)], ['23', '33'])).
% 0.22/0.53  thf('35', plain, ((v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.53      inference('demod', [status(thm)], ['20', '34'])).
% 0.22/0.53  thf('36', plain, ($false), inference('demod', [status(thm)], ['6', '35'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
