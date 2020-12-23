%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aHbgePf10k

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:29 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   70 (  97 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  422 ( 725 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_tex_2,axiom,(
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
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X15 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X17 )
       != ( sk_C @ X14 @ X15 ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X6 @ X5 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( sk_C @ X14 @ X15 ) @ X14 )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26','40'])).

thf('42',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['4','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aHbgePf10k
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:04:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.87  % Solved by: fo/fo7.sh
% 0.70/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.87  % done 570 iterations in 0.422s
% 0.70/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.87  % SZS output start Refutation
% 0.70/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.70/0.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.87  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.70/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.87  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.70/0.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.70/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.87  thf(t35_tex_2, conjecture,
% 0.70/0.87    (![A:$i]:
% 0.70/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.87       ( ![B:$i]:
% 0.70/0.87         ( ( ( v1_xboole_0 @ B ) & 
% 0.70/0.87             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.87           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.70/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.87    (~( ![A:$i]:
% 0.70/0.87        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.70/0.87            ( l1_pre_topc @ A ) ) =>
% 0.70/0.87          ( ![B:$i]:
% 0.70/0.87            ( ( ( v1_xboole_0 @ B ) & 
% 0.70/0.87                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.87              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.70/0.87    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.70/0.87  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf(l13_xboole_0, axiom,
% 0.70/0.87    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.87  thf('2', plain,
% 0.70/0.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.87  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.87  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.70/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.87  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('6', plain,
% 0.70/0.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.87  thf(t4_subset_1, axiom,
% 0.70/0.87    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.87  thf('7', plain,
% 0.70/0.87      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.70/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.87  thf('8', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.87      inference('sup+', [status(thm)], ['6', '7'])).
% 0.70/0.87  thf(cc1_tops_1, axiom,
% 0.70/0.87    (![A:$i]:
% 0.70/0.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.87       ( ![B:$i]:
% 0.70/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.87           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.70/0.87  thf('9', plain,
% 0.70/0.87      (![X12 : $i, X13 : $i]:
% 0.70/0.87         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.70/0.87          | (v3_pre_topc @ X12 @ X13)
% 0.70/0.87          | ~ (v1_xboole_0 @ X12)
% 0.70/0.87          | ~ (l1_pre_topc @ X13)
% 0.70/0.87          | ~ (v2_pre_topc @ X13))),
% 0.70/0.87      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.70/0.87  thf('10', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         (~ (v1_xboole_0 @ X1)
% 0.70/0.87          | ~ (v2_pre_topc @ X0)
% 0.70/0.87          | ~ (l1_pre_topc @ X0)
% 0.70/0.87          | ~ (v1_xboole_0 @ X1)
% 0.70/0.87          | (v3_pre_topc @ X1 @ X0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.70/0.87  thf('11', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         ((v3_pre_topc @ X1 @ X0)
% 0.70/0.87          | ~ (l1_pre_topc @ X0)
% 0.70/0.87          | ~ (v2_pre_topc @ X0)
% 0.70/0.87          | ~ (v1_xboole_0 @ X1))),
% 0.70/0.87      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.87  thf('12', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (~ (v1_xboole_0 @ X0)
% 0.70/0.87          | ~ (v2_pre_topc @ sk_A)
% 0.70/0.87          | (v3_pre_topc @ X0 @ sk_A))),
% 0.70/0.87      inference('sup-', [status(thm)], ['5', '11'])).
% 0.70/0.87  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('14', plain,
% 0.70/0.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('15', plain,
% 0.70/0.87      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.70/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.87  thf('16', plain,
% 0.70/0.87      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.70/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.87  thf(d5_tex_2, axiom,
% 0.70/0.87    (![A:$i]:
% 0.70/0.87     ( ( l1_pre_topc @ A ) =>
% 0.70/0.87       ( ![B:$i]:
% 0.70/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.87           ( ( v2_tex_2 @ B @ A ) <=>
% 0.70/0.87             ( ![C:$i]:
% 0.70/0.87               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.87                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.70/0.87                      ( ![D:$i]:
% 0.70/0.87                        ( ( m1_subset_1 @
% 0.70/0.87                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.87                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.70/0.87                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.70/0.87                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.87  thf('17', plain,
% 0.70/0.87      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.70/0.87         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.70/0.87          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.70/0.87          | ~ (v3_pre_topc @ X17 @ X15)
% 0.70/0.87          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ X14 @ X17)
% 0.70/0.87              != (sk_C @ X14 @ X15))
% 0.70/0.87          | (v2_tex_2 @ X14 @ X15)
% 0.70/0.87          | ~ (l1_pre_topc @ X15))),
% 0.70/0.87      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.70/0.87  thf('18', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         (~ (l1_pre_topc @ X0)
% 0.70/0.87          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.87          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.70/0.87              != (sk_C @ k1_xboole_0 @ X0))
% 0.70/0.87          | ~ (v3_pre_topc @ X1 @ X0)
% 0.70/0.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.70/0.87      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.87  thf('19', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.70/0.87          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.70/0.87              != (sk_C @ k1_xboole_0 @ X0))
% 0.70/0.87          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.87          | ~ (l1_pre_topc @ X0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['15', '18'])).
% 0.70/0.87  thf('20', plain,
% 0.70/0.87      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.70/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.87  thf(idempotence_k9_subset_1, axiom,
% 0.70/0.87    (![A:$i,B:$i,C:$i]:
% 0.70/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.87       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.70/0.87  thf('21', plain,
% 0.70/0.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.87         (((k9_subset_1 @ X6 @ X5 @ X5) = (X5))
% 0.70/0.87          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.70/0.87      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.70/0.87  thf('22', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.70/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.87  thf('23', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.70/0.87          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.70/0.87          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.87          | ~ (l1_pre_topc @ X0))),
% 0.70/0.87      inference('demod', [status(thm)], ['19', '22'])).
% 0.70/0.87  thf('24', plain,
% 0.70/0.87      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.87        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.87        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.70/0.87        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['14', '23'])).
% 0.70/0.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.70/0.87  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.87  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('27', plain,
% 0.70/0.87      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.70/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.87  thf('28', plain,
% 0.70/0.87      (![X14 : $i, X15 : $i]:
% 0.70/0.87         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.70/0.87          | (r1_tarski @ (sk_C @ X14 @ X15) @ X14)
% 0.70/0.87          | (v2_tex_2 @ X14 @ X15)
% 0.70/0.87          | ~ (l1_pre_topc @ X15))),
% 0.70/0.87      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.70/0.87  thf('29', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (~ (l1_pre_topc @ X0)
% 0.70/0.87          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.87          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.87  thf(l32_xboole_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.87  thf('30', plain,
% 0.70/0.87      (![X1 : $i, X3 : $i]:
% 0.70/0.87         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.70/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.87  thf('31', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.87          | ~ (l1_pre_topc @ X0)
% 0.70/0.87          | ((k4_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.70/0.87              = (k1_xboole_0)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['29', '30'])).
% 0.70/0.87  thf(t3_boole, axiom,
% 0.70/0.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.87  thf('32', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.70/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.87  thf('33', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.87          | ~ (l1_pre_topc @ X0)
% 0.70/0.87          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.70/0.87      inference('demod', [status(thm)], ['31', '32'])).
% 0.70/0.87  thf('34', plain,
% 0.70/0.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.87  thf('35', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.70/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.87  thf('36', plain,
% 0.70/0.87      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['34', '35'])).
% 0.70/0.87  thf('37', plain,
% 0.70/0.87      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.70/0.87        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.87        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['33', '36'])).
% 0.70/0.87  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.87  thf('40', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.70/0.87      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.70/0.87  thf('41', plain,
% 0.70/0.87      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.70/0.87      inference('demod', [status(thm)], ['24', '25', '26', '40'])).
% 0.70/0.87  thf('42', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.70/0.87      inference('simplify', [status(thm)], ['41'])).
% 0.70/0.87  thf('43', plain, ($false), inference('demod', [status(thm)], ['4', '42'])).
% 0.70/0.87  
% 0.70/0.87  % SZS output end Refutation
% 0.70/0.87  
% 0.70/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
