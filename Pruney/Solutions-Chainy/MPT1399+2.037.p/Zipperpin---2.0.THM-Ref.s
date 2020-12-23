%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1QVJ9M7HOZ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:07 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 102 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  441 (1197 expanded)
%              Number of equality atoms :    6 (  27 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('7',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( ~ ( v3_pre_topc @ X17 @ sk_A )
      | ~ ( v4_pre_topc @ X17 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X17 )
      | ( r2_hidden @ X17 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X17: $i] :
      ( ~ ( v3_pre_topc @ X17 @ sk_A )
      | ~ ( v4_pre_topc @ X17 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X17 )
      | ( r2_hidden @ X17 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('29',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('42',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1QVJ9M7HOZ
% 0.15/0.38  % Computer   : n009.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 19:46:11 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 82 iterations in 0.037s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.34/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.34/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.34/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(t28_connsp_2, conjecture,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53           ( ![C:$i]:
% 0.34/0.53             ( ( m1_subset_1 @
% 0.34/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.53               ( ~( ( ![D:$i]:
% 0.34/0.53                      ( ( m1_subset_1 @
% 0.34/0.53                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53                        ( ( r2_hidden @ D @ C ) <=>
% 0.34/0.53                          ( ( v3_pre_topc @ D @ A ) & 
% 0.34/0.53                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.34/0.53                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i]:
% 0.34/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.53            ( l1_pre_topc @ A ) ) =>
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.34/0.53              ( ![C:$i]:
% 0.34/0.53                ( ( m1_subset_1 @
% 0.34/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.53                  ( ~( ( ![D:$i]:
% 0.34/0.53                         ( ( m1_subset_1 @
% 0.34/0.53                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53                           ( ( r2_hidden @ D @ C ) <=>
% 0.34/0.53                             ( ( v3_pre_topc @ D @ A ) & 
% 0.34/0.53                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.34/0.53                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.34/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t2_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.34/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X7 : $i, X8 : $i]:
% 0.34/0.53         ((r2_hidden @ X7 @ X8)
% 0.34/0.53          | (v1_xboole_0 @ X8)
% 0.34/0.53          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.34/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf(fc10_tops_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X16 : $i]:
% 0.34/0.53         ((v3_pre_topc @ (k2_struct_0 @ X16) @ X16)
% 0.34/0.53          | ~ (l1_pre_topc @ X16)
% 0.34/0.53          | ~ (v2_pre_topc @ X16))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.34/0.53  thf(d3_struct_0, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X12 : $i]:
% 0.34/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.53  thf(fc4_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X15 : $i]:
% 0.34/0.53         ((v4_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.34/0.53          | ~ (l1_pre_topc @ X15)
% 0.34/0.53          | ~ (v2_pre_topc @ X15))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X12 : $i]:
% 0.34/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.53  thf(d3_tarski, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.34/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X4 : $i, X6 : $i]:
% 0.34/0.53         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X4 : $i, X6 : $i]:
% 0.34/0.53         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.53  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.34/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.34/0.53  thf(t3_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X9 : $i, X11 : $i]:
% 0.34/0.53         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.53  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X17 : $i]:
% 0.34/0.53         (~ (v3_pre_topc @ X17 @ sk_A)
% 0.34/0.53          | ~ (v4_pre_topc @ X17 @ sk_A)
% 0.34/0.53          | ~ (r2_hidden @ sk_B_1 @ X17)
% 0.34/0.53          | (r2_hidden @ X17 @ sk_C_1)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('15', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X17 : $i]:
% 0.34/0.53         (~ (v3_pre_topc @ X17 @ sk_A)
% 0.34/0.53          | ~ (v4_pre_topc @ X17 @ sk_A)
% 0.34/0.53          | ~ (r2_hidden @ sk_B_1 @ X17)
% 0.34/0.53          | (r2_hidden @ X17 @ k1_xboole_0)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.34/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '17'])).
% 0.34/0.53  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_l1_pre_topc, axiom,
% 0.34/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.34/0.53  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['6', '22'])).
% 0.34/0.53  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '26'])).
% 0.34/0.53  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['4', '29'])).
% 0.34/0.53  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.34/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.34/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '33'])).
% 0.34/0.53  thf(d1_xboole_0, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.34/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.34/0.53  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.34/0.53  thf('38', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.34/0.53  thf(fc2_struct_0, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.34/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (![X14 : $i]:
% 0.34/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.34/0.53          | ~ (l1_struct_0 @ X14)
% 0.34/0.53          | (v2_struct_0 @ X14))),
% 0.34/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.34/0.53  thf('40', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.34/0.53  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.53  thf('42', plain, ((v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.34/0.53  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
